%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:38 EST 2020

% Result     : Timeout 60.05s
% Output     : None 
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----No solution output by system
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.29  % Computer   : n007.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.29  % CPULimit   : 60
% 0.13/0.29  % WCLimit    : 600
% 0.13/0.29  % DateTime   : Tue Dec  1 14:43:21 EST 2020
% 0.13/0.29  % CPUTime    : 
% 0.13/0.29  # Version: 2.5pre002
% 0.13/0.29  # No SInE strategy applied
% 0.13/0.29  # Trying AutoSched0 for 299 seconds
% 60.05/60.23  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 60.05/60.23  # and selection function SelectComplexExceptUniqMaxHorn.
% 60.05/60.23  #
% 60.05/60.23  # Preprocessing time       : 0.016 s
% 60.05/60.23  # Presaturation interreduction done
% 60.05/60.24  
% 60.05/60.24  # Failure: Resource limit exceeded (time)
% 60.05/60.24  # SZS status ResourceOut
% 60.05/60.24  eprover: CPU time limit exceeded, terminating
%------------------------------------------------------------------------------
