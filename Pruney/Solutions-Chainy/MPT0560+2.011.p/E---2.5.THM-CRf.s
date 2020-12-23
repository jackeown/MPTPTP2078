%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:08 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 177 expanded)
%              Number of clauses        :   42 (  79 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 334 expanded)
%              Number of equality atoms :   52 ( 114 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t162_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(t159_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k9_relat_1(k5_relat_1(X2,X3),X1) = k9_relat_1(X3,k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_12,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | v1_relat_1(k7_relat_1(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_13,plain,(
    ! [X9] : v1_relat_1(k6_relat_1(X9)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_14,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | k7_relat_1(k5_relat_1(X13,X14),X12) = k5_relat_1(k7_relat_1(X13,X12),X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

fof(c_0_15,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(k1_relat_1(X26),X25)
      | k7_relat_1(X26,X25) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_16,plain,(
    ! [X20] :
      ( k1_relat_1(k6_relat_1(X20)) = X20
      & k2_relat_1(k6_relat_1(X20)) = X20 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2,X3] :
            ( r1_tarski(X2,X3)
           => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t162_relat_1])).

fof(c_0_18,plain,(
    ! [X27] :
      ( ~ v1_relat_1(X27)
      | k7_relat_1(X27,k1_relat_1(X27)) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_19,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | k7_relat_1(X24,X23) = k5_relat_1(k6_relat_1(X23),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_22,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & r1_tarski(esk2_0,esk3_0)
    & k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_26,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k7_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X3) = k5_relat_1(k7_relat_1(X1,X3),k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_30,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_20])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(k5_relat_1(X22,k6_relat_1(X21)),X22)
        | ~ v1_relat_1(X22) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X21),X22),X22)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

cnf(c_0_33,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_20])).

cnf(c_0_35,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X3),k6_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk2_0),esk3_0) = k6_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k9_relat_1(k5_relat_1(X18,X19),X17) = k9_relat_1(X19,k9_relat_1(X18,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_relat_1])])])).

fof(c_0_38,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k2_relat_1(k7_relat_1(X16,X15)) = k9_relat_1(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk3_0),k6_relat_1(esk2_0)) = k6_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,plain,
    ( k9_relat_1(k5_relat_1(X1,X2),X3) = k9_relat_1(X2,k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_45,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_46,plain,
    ( r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3)),k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( k5_relat_1(k7_relat_1(k6_relat_1(esk3_0),esk2_0),k6_relat_1(esk2_0)) = k6_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24])).

cnf(c_0_48,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k7_relat_1(esk1_0,X1) = k5_relat_1(k6_relat_1(X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(k5_relat_1(X1,esk1_0),X2) = k5_relat_1(k7_relat_1(X1,X2),esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( k9_relat_1(k5_relat_1(X1,esk1_0),X2) = k9_relat_1(esk1_0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk1_0,X1)) = k9_relat_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_42])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k6_relat_1(esk2_0),k7_relat_1(k6_relat_1(esk3_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),esk1_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( k9_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0),X2) = k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( k9_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk1_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0)) = k9_relat_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( k6_relat_1(esk2_0) = k7_relat_1(k6_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_64,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),esk1_0)) = k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(X1),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0)) != k9_relat_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:47:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.41/0.57  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 0.41/0.57  # and selection function SelectComplexG.
% 0.41/0.57  #
% 0.41/0.57  # Preprocessing time       : 0.023 s
% 0.41/0.57  # Presaturation interreduction done
% 0.41/0.57  
% 0.41/0.57  # Proof found!
% 0.41/0.57  # SZS status Theorem
% 0.41/0.57  # SZS output start CNFRefutation
% 0.41/0.57  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.41/0.57  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.41/0.57  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 0.41/0.57  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.41/0.57  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.41/0.57  fof(t162_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.41/0.57  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.41/0.57  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.41/0.57  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.41/0.57  fof(t159_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k9_relat_1(k5_relat_1(X2,X3),X1)=k9_relat_1(X3,k9_relat_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 0.41/0.57  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.41/0.57  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.41/0.57  fof(c_0_12, plain, ![X10, X11]:(~v1_relat_1(X10)|v1_relat_1(k7_relat_1(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.41/0.57  fof(c_0_13, plain, ![X9]:v1_relat_1(k6_relat_1(X9)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.41/0.57  fof(c_0_14, plain, ![X12, X13, X14]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|k7_relat_1(k5_relat_1(X13,X14),X12)=k5_relat_1(k7_relat_1(X13,X12),X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.41/0.57  fof(c_0_15, plain, ![X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(k1_relat_1(X26),X25)|k7_relat_1(X26,X25)=X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.41/0.57  fof(c_0_16, plain, ![X20]:(k1_relat_1(k6_relat_1(X20))=X20&k2_relat_1(k6_relat_1(X20))=X20), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.41/0.57  fof(c_0_17, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)))), inference(assume_negation,[status(cth)],[t162_relat_1])).
% 0.41/0.57  fof(c_0_18, plain, ![X27]:(~v1_relat_1(X27)|k7_relat_1(X27,k1_relat_1(X27))=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.41/0.57  cnf(c_0_19, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.41/0.57  cnf(c_0_20, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.41/0.57  fof(c_0_21, plain, ![X23, X24]:(~v1_relat_1(X24)|k7_relat_1(X24,X23)=k5_relat_1(k6_relat_1(X23),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.41/0.57  cnf(c_0_22, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.41/0.57  cnf(c_0_23, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.41/0.57  cnf(c_0_24, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.41/0.57  fof(c_0_25, negated_conjecture, (v1_relat_1(esk1_0)&(r1_tarski(esk2_0,esk3_0)&k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.41/0.57  cnf(c_0_26, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.41/0.57  cnf(c_0_27, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.41/0.57  cnf(c_0_28, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.41/0.57  cnf(c_0_29, plain, (k7_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X3)=k5_relat_1(k7_relat_1(X1,X3),k6_relat_1(X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.41/0.57  cnf(c_0_30, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_20])])).
% 0.41/0.57  cnf(c_0_31, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.41/0.57  fof(c_0_32, plain, ![X21, X22]:((r1_tarski(k5_relat_1(X22,k6_relat_1(X21)),X22)|~v1_relat_1(X22))&(r1_tarski(k5_relat_1(k6_relat_1(X21),X22),X22)|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.41/0.57  cnf(c_0_33, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.41/0.57  cnf(c_0_34, plain, (k7_relat_1(k6_relat_1(X1),X2)=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_20])).
% 0.41/0.57  cnf(c_0_35, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)=k5_relat_1(k7_relat_1(k6_relat_1(X1),X3),k6_relat_1(X2))), inference(spm,[status(thm)],[c_0_29, c_0_20])).
% 0.41/0.57  cnf(c_0_36, negated_conjecture, (k7_relat_1(k6_relat_1(esk2_0),esk3_0)=k6_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.41/0.57  fof(c_0_37, plain, ![X17, X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|k9_relat_1(k5_relat_1(X18,X19),X17)=k9_relat_1(X19,k9_relat_1(X18,X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_relat_1])])])).
% 0.41/0.57  fof(c_0_38, plain, ![X15, X16]:(~v1_relat_1(X16)|k2_relat_1(k7_relat_1(X16,X15))=k9_relat_1(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.41/0.57  cnf(c_0_39, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.57  cnf(c_0_40, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.41/0.57  cnf(c_0_41, negated_conjecture, (k5_relat_1(k6_relat_1(esk3_0),k6_relat_1(esk2_0))=k6_relat_1(esk2_0)), inference(rw,[status(thm)],[c_0_36, c_0_34])).
% 0.41/0.57  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.41/0.57  cnf(c_0_43, plain, (k9_relat_1(k5_relat_1(X1,X2),X3)=k9_relat_1(X2,k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.41/0.57  cnf(c_0_44, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.41/0.57  fof(c_0_45, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.41/0.57  cnf(c_0_46, plain, (r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3)),k7_relat_1(k6_relat_1(X1),X2))), inference(spm,[status(thm)],[c_0_39, c_0_27])).
% 0.41/0.57  cnf(c_0_47, negated_conjecture, (k5_relat_1(k7_relat_1(k6_relat_1(esk3_0),esk2_0),k6_relat_1(esk2_0))=k6_relat_1(esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_24])).
% 0.41/0.57  cnf(c_0_48, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_20])).
% 0.41/0.57  cnf(c_0_49, negated_conjecture, (v1_relat_1(k7_relat_1(esk1_0,X1))), inference(spm,[status(thm)],[c_0_19, c_0_42])).
% 0.41/0.57  cnf(c_0_50, negated_conjecture, (k7_relat_1(esk1_0,X1)=k5_relat_1(k6_relat_1(X1),esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_42])).
% 0.41/0.57  cnf(c_0_51, negated_conjecture, (k7_relat_1(k5_relat_1(X1,esk1_0),X2)=k5_relat_1(k7_relat_1(X1,X2),esk1_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_42])).
% 0.41/0.57  cnf(c_0_52, negated_conjecture, (k9_relat_1(k5_relat_1(X1,esk1_0),X2)=k9_relat_1(esk1_0,k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 0.41/0.57  cnf(c_0_53, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.41/0.57  cnf(c_0_54, negated_conjecture, (k2_relat_1(k7_relat_1(esk1_0,X1))=k9_relat_1(esk1_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_42])).
% 0.41/0.57  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.41/0.57  cnf(c_0_56, negated_conjecture, (r1_tarski(k6_relat_1(esk2_0),k7_relat_1(k6_relat_1(esk3_0),esk2_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.41/0.57  cnf(c_0_57, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2))), inference(spm,[status(thm)],[c_0_48, c_0_34])).
% 0.41/0.57  cnf(c_0_58, negated_conjecture, (v1_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.41/0.57  cnf(c_0_59, negated_conjecture, (k7_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0),X2)=k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),esk1_0)), inference(spm,[status(thm)],[c_0_51, c_0_20])).
% 0.41/0.57  cnf(c_0_60, negated_conjecture, (k9_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0),X2)=k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(X1),X2))), inference(spm,[status(thm)],[c_0_52, c_0_20])).
% 0.41/0.57  cnf(c_0_61, negated_conjecture, (k9_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk1_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_53, c_0_50])).
% 0.41/0.57  cnf(c_0_62, negated_conjecture, (k2_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0))=k9_relat_1(esk1_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_50])).
% 0.41/0.57  cnf(c_0_63, negated_conjecture, (k6_relat_1(esk2_0)=k7_relat_1(k6_relat_1(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.41/0.57  cnf(c_0_64, negated_conjecture, (k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),esk1_0))=k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(X1),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_58]), c_0_59]), c_0_60])).
% 0.41/0.57  cnf(c_0_65, negated_conjecture, (k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0))!=k9_relat_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_61, c_0_60])).
% 0.41/0.57  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65]), ['proof']).
% 0.41/0.57  # SZS output end CNFRefutation
% 0.41/0.57  # Proof object total steps             : 67
% 0.41/0.57  # Proof object clause steps            : 42
% 0.41/0.57  # Proof object formula steps           : 25
% 0.41/0.57  # Proof object conjectures             : 24
% 0.41/0.57  # Proof object clause conjectures      : 21
% 0.41/0.57  # Proof object formula conjectures     : 3
% 0.41/0.57  # Proof object initial clauses used    : 14
% 0.41/0.57  # Proof object initial formulas used   : 12
% 0.41/0.57  # Proof object generating inferences   : 25
% 0.41/0.57  # Proof object simplifying inferences  : 13
% 0.41/0.57  # Training examples: 0 positive, 0 negative
% 0.41/0.57  # Parsed axioms                        : 13
% 0.41/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.41/0.57  # Initial clauses                      : 19
% 0.41/0.57  # Removed in clause preprocessing      : 0
% 0.41/0.57  # Initial clauses in saturation        : 19
% 0.41/0.57  # Processed clauses                    : 2930
% 0.41/0.57  # ...of these trivial                  : 262
% 0.41/0.57  # ...subsumed                          : 1553
% 0.41/0.57  # ...remaining for further processing  : 1115
% 0.41/0.57  # Other redundant clauses eliminated   : 2
% 0.41/0.57  # Clauses deleted for lack of memory   : 0
% 0.41/0.57  # Backward-subsumed                    : 46
% 0.41/0.57  # Backward-rewritten                   : 276
% 0.41/0.57  # Generated clauses                    : 14629
% 0.41/0.57  # ...of the previous two non-trivial   : 11376
% 0.41/0.57  # Contextual simplify-reflections      : 0
% 0.41/0.57  # Paramodulations                      : 14627
% 0.41/0.57  # Factorizations                       : 0
% 0.41/0.57  # Equation resolutions                 : 2
% 0.41/0.57  # Propositional unsat checks           : 0
% 0.41/0.57  #    Propositional check models        : 0
% 0.41/0.57  #    Propositional check unsatisfiable : 0
% 0.41/0.57  #    Propositional clauses             : 0
% 0.41/0.57  #    Propositional clauses after purity: 0
% 0.41/0.57  #    Propositional unsat core size     : 0
% 0.41/0.57  #    Propositional preprocessing time  : 0.000
% 0.41/0.57  #    Propositional encoding time       : 0.000
% 0.41/0.57  #    Propositional solver time         : 0.000
% 0.41/0.57  #    Success case prop preproc time    : 0.000
% 0.41/0.57  #    Success case prop encoding time   : 0.000
% 0.41/0.57  #    Success case prop solver time     : 0.000
% 0.41/0.57  # Current number of processed clauses  : 773
% 0.41/0.57  #    Positive orientable unit clauses  : 402
% 0.41/0.57  #    Positive unorientable unit clauses: 13
% 0.41/0.57  #    Negative unit clauses             : 1
% 0.41/0.57  #    Non-unit-clauses                  : 357
% 0.41/0.57  # Current number of unprocessed clauses: 8185
% 0.41/0.57  # ...number of literals in the above   : 10503
% 0.41/0.57  # Current number of archived formulas  : 0
% 0.41/0.57  # Current number of archived clauses   : 340
% 0.41/0.57  # Clause-clause subsumption calls (NU) : 71351
% 0.41/0.57  # Rec. Clause-clause subsumption calls : 59894
% 0.41/0.57  # Non-unit clause-clause subsumptions  : 1582
% 0.41/0.57  # Unit Clause-clause subsumption calls : 67
% 0.41/0.57  # Rewrite failures with RHS unbound    : 0
% 0.41/0.57  # BW rewrite match attempts            : 1459
% 0.41/0.57  # BW rewrite match successes           : 142
% 0.41/0.57  # Condensation attempts                : 0
% 0.41/0.57  # Condensation successes               : 0
% 0.41/0.57  # Termbank termtop insertions          : 247586
% 0.41/0.57  
% 0.41/0.57  # -------------------------------------------------
% 0.41/0.57  # User time                : 0.228 s
% 0.41/0.57  # System time              : 0.010 s
% 0.41/0.57  # Total time               : 0.238 s
% 0.41/0.57  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
