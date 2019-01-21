-- -*- coding: utf-8 -*-
-- Copyright: © 2019 Simon Nielsen Knights <tauoverpi@yandex.com>
-- License  : GNU AGPL, version 3 or later; http://www.gnu.org/licenses/agpl.html

module DCTP.Syntax

import DCTP.Core
import DCTP.Event

%default total
%access public export

syntax ifW [pred] "then" [consequent] "else" [alternate] =
  decide pred consequent alternate
