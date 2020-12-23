%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:58 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 157 expanded)
%              Number of clauses        :   25 (  49 expanded)
%              Number of leaves         :    3 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :  236 (1505 expanded)
%              Number of equality atoms :   35 ( 269 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
               => ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X1)
                   => ( X4 = X5
                      | ( r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)
                        & k1_funct_1(X3,X4) != k1_funct_1(X3,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_wellord1)).

fof(d7_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
              <=> ( k1_relat_1(X3) = k3_relat_1(X1)
                  & k2_relat_1(X3) = k3_relat_1(X2)
                  & v2_funct_1(X3)
                  & ! [X4,X5] :
                      ( r2_hidden(k4_tarski(X4,X5),X1)
                    <=> ( r2_hidden(X4,k3_relat_1(X1))
                        & r2_hidden(X5,k3_relat_1(X1))
                        & r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_wellord1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( r3_wellord1(X1,X2,X3)
                 => ! [X4,X5] :
                      ( r2_hidden(k4_tarski(X4,X5),X1)
                     => ( X4 = X5
                        | ( r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)
                          & k1_funct_1(X3,X4) != k1_funct_1(X3,X5) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t45_wellord1])).

fof(c_0_4,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17] :
      ( ( k1_relat_1(X13) = k3_relat_1(X11)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( k2_relat_1(X13) = k3_relat_1(X12)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( v2_funct_1(X13)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(X14,k3_relat_1(X11))
        | ~ r2_hidden(k4_tarski(X14,X15),X11)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(X15,k3_relat_1(X11))
        | ~ r2_hidden(k4_tarski(X14,X15),X11)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X13,X14),k1_funct_1(X13,X15)),X12)
        | ~ r2_hidden(k4_tarski(X14,X15),X11)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(X16,k3_relat_1(X11))
        | ~ r2_hidden(X17,k3_relat_1(X11))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X13,X16),k1_funct_1(X13,X17)),X12)
        | r2_hidden(k4_tarski(X16,X17),X11)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk3_3(X11,X12,X13),esk4_3(X11,X12,X13)),X11)
        | ~ r2_hidden(esk3_3(X11,X12,X13),k3_relat_1(X11))
        | ~ r2_hidden(esk4_3(X11,X12,X13),k3_relat_1(X11))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X13,esk3_3(X11,X12,X13)),k1_funct_1(X13,esk4_3(X11,X12,X13))),X12)
        | k1_relat_1(X13) != k3_relat_1(X11)
        | k2_relat_1(X13) != k3_relat_1(X12)
        | ~ v2_funct_1(X13)
        | r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk3_3(X11,X12,X13),k3_relat_1(X11))
        | r2_hidden(k4_tarski(esk3_3(X11,X12,X13),esk4_3(X11,X12,X13)),X11)
        | k1_relat_1(X13) != k3_relat_1(X11)
        | k2_relat_1(X13) != k3_relat_1(X12)
        | ~ v2_funct_1(X13)
        | r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk4_3(X11,X12,X13),k3_relat_1(X11))
        | r2_hidden(k4_tarski(esk3_3(X11,X12,X13),esk4_3(X11,X12,X13)),X11)
        | k1_relat_1(X13) != k3_relat_1(X11)
        | k2_relat_1(X13) != k3_relat_1(X12)
        | ~ v2_funct_1(X13)
        | r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X13,esk3_3(X11,X12,X13)),k1_funct_1(X13,esk4_3(X11,X12,X13))),X12)
        | r2_hidden(k4_tarski(esk3_3(X11,X12,X13),esk4_3(X11,X12,X13)),X11)
        | k1_relat_1(X13) != k3_relat_1(X11)
        | k2_relat_1(X13) != k3_relat_1(X12)
        | ~ v2_funct_1(X13)
        | r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_wellord1])])])])])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_relat_1(esk6_0)
    & v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & r3_wellord1(esk5_0,esk6_0,esk7_0)
    & r2_hidden(k4_tarski(esk8_0,esk9_0),esk5_0)
    & esk8_0 != esk9_0
    & ( ~ r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk8_0),k1_funct_1(esk7_0,esk9_0)),esk6_0)
      | k1_funct_1(esk7_0,esk8_0) = k1_funct_1(esk7_0,esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v2_funct_1(X6)
        | ~ r2_hidden(X7,k1_relat_1(X6))
        | ~ r2_hidden(X8,k1_relat_1(X6))
        | k1_funct_1(X6,X7) != k1_funct_1(X6,X8)
        | X7 = X8
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk1_1(X6),k1_relat_1(X6))
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk2_1(X6),k1_relat_1(X6))
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( k1_funct_1(X6,esk1_1(X6)) = k1_funct_1(X6,esk2_1(X6))
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( esk1_1(X6) != esk2_1(X6)
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_7,plain,
    ( k1_relat_1(X1) = k3_relat_1(X2)
    | ~ r3_wellord1(X2,X3,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r3_wellord1(esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( v2_funct_1(X1)
    | ~ r3_wellord1(X2,X3,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3)),X4)
    | ~ r2_hidden(k4_tarski(X2,X3),X5)
    | ~ r3_wellord1(X5,X4,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r3_wellord1(X2,X4,X5)
    | ~ v1_relat_1(X5)
    | ~ v1_funct_1(X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( k1_relat_1(esk7_0) = k3_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_19,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_20,negated_conjecture,
    ( k1_funct_1(esk7_0,esk8_0) = k1_funct_1(esk7_0,esk9_0)
    | ~ r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk8_0),k1_funct_1(esk7_0,esk9_0)),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(X1,esk8_0),k1_funct_1(X1,esk9_0)),X2)
    | ~ r3_wellord1(esk5_0,X2,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_11])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk9_0,k3_relat_1(esk5_0))
    | ~ r3_wellord1(esk5_0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_15]),c_0_11])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r3_wellord1(X2,X4,X5)
    | ~ v1_relat_1(X5)
    | ~ v1_funct_1(X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk7_0,X1) != k1_funct_1(esk7_0,X2)
    | ~ r2_hidden(X2,k3_relat_1(esk5_0))
    | ~ r2_hidden(X1,k3_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_9]),c_0_12])])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(esk7_0,esk9_0) = k1_funct_1(esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_8]),c_0_9]),c_0_10]),c_0_12])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk9_0,k3_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_8]),c_0_9]),c_0_12]),c_0_10])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk8_0,k3_relat_1(esk5_0))
    | ~ r3_wellord1(esk5_0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_15]),c_0_11])])).

cnf(c_0_28,negated_conjecture,
    ( esk9_0 = X1
    | k1_funct_1(esk7_0,esk8_0) != k1_funct_1(esk7_0,X1)
    | ~ r2_hidden(X1,k3_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk8_0,k3_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_8]),c_0_9]),c_0_12]),c_0_10])])).

cnf(c_0_30,negated_conjecture,
    ( esk8_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:04:49 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.028 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t45_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X1)=>(X4=X5|(r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)&k1_funct_1(X3,X4)!=k1_funct_1(X3,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_wellord1)).
% 0.12/0.36  fof(d7_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)<=>(((k1_relat_1(X3)=k3_relat_1(X1)&k2_relat_1(X3)=k3_relat_1(X2))&v2_funct_1(X3))&![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X1)<=>((r2_hidden(X4,k3_relat_1(X1))&r2_hidden(X5,k3_relat_1(X1)))&r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_wellord1)).
% 0.12/0.36  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 0.12/0.36  fof(c_0_3, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X1)=>(X4=X5|(r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)&k1_funct_1(X3,X4)!=k1_funct_1(X3,X5))))))))), inference(assume_negation,[status(cth)],[t45_wellord1])).
% 0.12/0.36  fof(c_0_4, plain, ![X11, X12, X13, X14, X15, X16, X17]:(((((k1_relat_1(X13)=k3_relat_1(X11)|~r3_wellord1(X11,X12,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v1_relat_1(X12)|~v1_relat_1(X11))&(k2_relat_1(X13)=k3_relat_1(X12)|~r3_wellord1(X11,X12,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v1_relat_1(X12)|~v1_relat_1(X11)))&(v2_funct_1(X13)|~r3_wellord1(X11,X12,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v1_relat_1(X12)|~v1_relat_1(X11)))&((((r2_hidden(X14,k3_relat_1(X11))|~r2_hidden(k4_tarski(X14,X15),X11)|~r3_wellord1(X11,X12,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v1_relat_1(X12)|~v1_relat_1(X11))&(r2_hidden(X15,k3_relat_1(X11))|~r2_hidden(k4_tarski(X14,X15),X11)|~r3_wellord1(X11,X12,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v1_relat_1(X12)|~v1_relat_1(X11)))&(r2_hidden(k4_tarski(k1_funct_1(X13,X14),k1_funct_1(X13,X15)),X12)|~r2_hidden(k4_tarski(X14,X15),X11)|~r3_wellord1(X11,X12,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v1_relat_1(X12)|~v1_relat_1(X11)))&(~r2_hidden(X16,k3_relat_1(X11))|~r2_hidden(X17,k3_relat_1(X11))|~r2_hidden(k4_tarski(k1_funct_1(X13,X16),k1_funct_1(X13,X17)),X12)|r2_hidden(k4_tarski(X16,X17),X11)|~r3_wellord1(X11,X12,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v1_relat_1(X12)|~v1_relat_1(X11))))&((~r2_hidden(k4_tarski(esk3_3(X11,X12,X13),esk4_3(X11,X12,X13)),X11)|(~r2_hidden(esk3_3(X11,X12,X13),k3_relat_1(X11))|~r2_hidden(esk4_3(X11,X12,X13),k3_relat_1(X11))|~r2_hidden(k4_tarski(k1_funct_1(X13,esk3_3(X11,X12,X13)),k1_funct_1(X13,esk4_3(X11,X12,X13))),X12))|(k1_relat_1(X13)!=k3_relat_1(X11)|k2_relat_1(X13)!=k3_relat_1(X12)|~v2_funct_1(X13))|r3_wellord1(X11,X12,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v1_relat_1(X12)|~v1_relat_1(X11))&(((r2_hidden(esk3_3(X11,X12,X13),k3_relat_1(X11))|r2_hidden(k4_tarski(esk3_3(X11,X12,X13),esk4_3(X11,X12,X13)),X11)|(k1_relat_1(X13)!=k3_relat_1(X11)|k2_relat_1(X13)!=k3_relat_1(X12)|~v2_funct_1(X13))|r3_wellord1(X11,X12,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v1_relat_1(X12)|~v1_relat_1(X11))&(r2_hidden(esk4_3(X11,X12,X13),k3_relat_1(X11))|r2_hidden(k4_tarski(esk3_3(X11,X12,X13),esk4_3(X11,X12,X13)),X11)|(k1_relat_1(X13)!=k3_relat_1(X11)|k2_relat_1(X13)!=k3_relat_1(X12)|~v2_funct_1(X13))|r3_wellord1(X11,X12,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v1_relat_1(X12)|~v1_relat_1(X11)))&(r2_hidden(k4_tarski(k1_funct_1(X13,esk3_3(X11,X12,X13)),k1_funct_1(X13,esk4_3(X11,X12,X13))),X12)|r2_hidden(k4_tarski(esk3_3(X11,X12,X13),esk4_3(X11,X12,X13)),X11)|(k1_relat_1(X13)!=k3_relat_1(X11)|k2_relat_1(X13)!=k3_relat_1(X12)|~v2_funct_1(X13))|r3_wellord1(X11,X12,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v1_relat_1(X12)|~v1_relat_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_wellord1])])])])])])).
% 0.12/0.36  fof(c_0_5, negated_conjecture, (v1_relat_1(esk5_0)&(v1_relat_1(esk6_0)&((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&(r3_wellord1(esk5_0,esk6_0,esk7_0)&(r2_hidden(k4_tarski(esk8_0,esk9_0),esk5_0)&(esk8_0!=esk9_0&(~r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk8_0),k1_funct_1(esk7_0,esk9_0)),esk6_0)|k1_funct_1(esk7_0,esk8_0)=k1_funct_1(esk7_0,esk9_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.12/0.36  fof(c_0_6, plain, ![X6, X7, X8]:((~v2_funct_1(X6)|(~r2_hidden(X7,k1_relat_1(X6))|~r2_hidden(X8,k1_relat_1(X6))|k1_funct_1(X6,X7)!=k1_funct_1(X6,X8)|X7=X8)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&((((r2_hidden(esk1_1(X6),k1_relat_1(X6))|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(r2_hidden(esk2_1(X6),k1_relat_1(X6))|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(k1_funct_1(X6,esk1_1(X6))=k1_funct_1(X6,esk2_1(X6))|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(esk1_1(X6)!=esk2_1(X6)|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.12/0.36  cnf(c_0_7, plain, (k1_relat_1(X1)=k3_relat_1(X2)|~r3_wellord1(X2,X3,X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_8, negated_conjecture, (r3_wellord1(esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_9, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_10, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_13, plain, (v2_funct_1(X1)|~r3_wellord1(X2,X3,X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_14, plain, (r2_hidden(k4_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3)),X4)|~r2_hidden(k4_tarski(X2,X3),X5)|~r3_wellord1(X5,X4,X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_15, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk9_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_16, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r3_wellord1(X2,X4,X5)|~v1_relat_1(X5)|~v1_funct_1(X5)|~v1_relat_1(X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_17, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_18, negated_conjecture, (k1_relat_1(esk7_0)=k3_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])])).
% 0.12/0.36  cnf(c_0_19, negated_conjecture, (v2_funct_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (k1_funct_1(esk7_0,esk8_0)=k1_funct_1(esk7_0,esk9_0)|~r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk8_0),k1_funct_1(esk7_0,esk9_0)),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_21, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(X1,esk8_0),k1_funct_1(X1,esk9_0)),X2)|~r3_wellord1(esk5_0,X2,X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_11])])).
% 0.12/0.36  cnf(c_0_22, negated_conjecture, (r2_hidden(esk9_0,k3_relat_1(esk5_0))|~r3_wellord1(esk5_0,X1,X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_15]), c_0_11])])).
% 0.12/0.36  cnf(c_0_23, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r3_wellord1(X2,X4,X5)|~v1_relat_1(X5)|~v1_funct_1(X5)|~v1_relat_1(X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_24, negated_conjecture, (X1=X2|k1_funct_1(esk7_0,X1)!=k1_funct_1(esk7_0,X2)|~r2_hidden(X2,k3_relat_1(esk5_0))|~r2_hidden(X1,k3_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_9]), c_0_12])])).
% 0.12/0.36  cnf(c_0_25, negated_conjecture, (k1_funct_1(esk7_0,esk9_0)=k1_funct_1(esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_8]), c_0_9]), c_0_10]), c_0_12])])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, (r2_hidden(esk9_0,k3_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_8]), c_0_9]), c_0_12]), c_0_10])])).
% 0.12/0.36  cnf(c_0_27, negated_conjecture, (r2_hidden(esk8_0,k3_relat_1(esk5_0))|~r3_wellord1(esk5_0,X1,X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_15]), c_0_11])])).
% 0.12/0.36  cnf(c_0_28, negated_conjecture, (esk9_0=X1|k1_funct_1(esk7_0,esk8_0)!=k1_funct_1(esk7_0,X1)|~r2_hidden(X1,k3_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.12/0.36  cnf(c_0_29, negated_conjecture, (r2_hidden(esk8_0,k3_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_8]), c_0_9]), c_0_12]), c_0_10])])).
% 0.12/0.36  cnf(c_0_30, negated_conjecture, (esk8_0!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_29])]), c_0_30]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 32
% 0.12/0.36  # Proof object clause steps            : 25
% 0.12/0.36  # Proof object formula steps           : 7
% 0.12/0.36  # Proof object conjectures             : 22
% 0.12/0.36  # Proof object clause conjectures      : 19
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 14
% 0.12/0.36  # Proof object initial formulas used   : 3
% 0.12/0.36  # Proof object generating inferences   : 11
% 0.12/0.36  # Proof object simplifying inferences  : 38
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 3
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 24
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 24
% 0.12/0.36  # Processed clauses                    : 59
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 59
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 3
% 0.12/0.36  # Generated clauses                    : 28
% 0.12/0.36  # ...of the previous two non-trivial   : 23
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 26
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 2
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 32
% 0.12/0.36  #    Positive orientable unit clauses  : 12
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 1
% 0.12/0.36  #    Non-unit-clauses                  : 19
% 0.12/0.36  # Current number of unprocessed clauses: 12
% 0.12/0.36  # ...number of literals in the above   : 87
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 27
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 882
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 16
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 36
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 3
% 0.12/0.36  # BW rewrite match successes           : 3
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 3547
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.031 s
% 0.12/0.36  # System time              : 0.005 s
% 0.12/0.36  # Total time               : 0.036 s
% 0.12/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
