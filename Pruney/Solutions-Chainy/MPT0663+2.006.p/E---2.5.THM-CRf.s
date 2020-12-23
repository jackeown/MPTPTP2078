%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:12 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 469 expanded)
%              Number of clauses        :   32 ( 181 expanded)
%              Number of leaves         :   14 ( 141 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 603 expanded)
%              Number of equality atoms :   41 ( 439 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   13 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t70_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(t40_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
         => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t71_funct_1])).

fof(c_0_15,plain,(
    ! [X29,X30] : k1_setfam_1(k2_tarski(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r2_hidden(esk1_0,k3_xboole_0(k1_relat_1(esk3_0),esk2_0))
    & k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0) != k1_funct_1(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X18,X19,X20,X21,X22] : k4_enumset1(X18,X18,X19,X20,X21,X22) = k3_enumset1(X18,X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_23,plain,(
    ! [X23,X24,X25,X26,X27,X28] : k5_enumset1(X23,X23,X24,X25,X26,X27,X28) = k4_enumset1(X23,X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_24,plain,(
    ! [X7,X8] : k2_tarski(X7,X8) = k2_tarski(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_25,plain,(
    ! [X39,X40] : k5_relat_1(k6_relat_1(X40),k6_relat_1(X39)) = k6_relat_1(k3_xboole_0(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_0,k3_xboole_0(k1_relat_1(esk3_0),esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X31] :
      ( k1_relat_1(k6_relat_1(X31)) = X31
      & k2_relat_1(k6_relat_1(X31)) = X31 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_34,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X41,X42,X43] :
      ( ~ v1_relat_1(X43)
      | ~ v1_funct_1(X43)
      | ~ r2_hidden(X41,k1_relat_1(k7_relat_1(X43,X42)))
      | k1_funct_1(k7_relat_1(X43,X42),X41) = k1_funct_1(X43,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_0,k1_setfam_1(k5_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_19]),c_0_19]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_38,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0) != k1_funct_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_44,plain,(
    ! [X32,X33,X34] :
      ( ( r2_hidden(X32,X33)
        | ~ r2_hidden(X32,k1_relat_1(k7_relat_1(X34,X33)))
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(X32,k1_relat_1(X34))
        | ~ r2_hidden(X32,k1_relat_1(k7_relat_1(X34,X33)))
        | ~ v1_relat_1(X34) )
      & ( ~ r2_hidden(X32,X33)
        | ~ r2_hidden(X32,k1_relat_1(X34))
        | r2_hidden(X32,k1_relat_1(k7_relat_1(X34,X33)))
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

fof(c_0_45,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(X36,k1_relat_1(X38))
        | ~ r2_hidden(X36,k1_relat_1(k5_relat_1(X38,k6_relat_1(X37))))
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( r2_hidden(k1_funct_1(X38,X36),X37)
        | ~ r2_hidden(X36,k1_relat_1(k5_relat_1(X38,k6_relat_1(X37))))
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( ~ r2_hidden(X36,k1_relat_1(X38))
        | ~ r2_hidden(k1_funct_1(X38,X36),X37)
        | r2_hidden(X36,k1_relat_1(k5_relat_1(X38,k6_relat_1(X37))))
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_funct_1])])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_0,k1_setfam_1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_39])).

fof(c_0_49,plain,(
    ! [X35] :
      ( v1_relat_1(k6_relat_1(X35))
      & v1_funct_1(k6_relat_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,k6_relat_1(X3))))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(k1_relat_1(esk3_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_54,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(esk3_0))
    | ~ r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_43])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_38]),c_0_54]),c_0_55])])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_48]),c_0_38]),c_0_54]),c_0_55])])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_53]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:36:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t71_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 0.12/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.37  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.12/0.37  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.12/0.37  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.12/0.37  fof(t70_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 0.12/0.37  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 0.12/0.37  fof(t40_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_1)).
% 0.12/0.37  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.12/0.37  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1)))), inference(assume_negation,[status(cth)],[t71_funct_1])).
% 0.12/0.37  fof(c_0_15, plain, ![X29, X30]:k1_setfam_1(k2_tarski(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.37  fof(c_0_16, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  fof(c_0_17, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r2_hidden(esk1_0,k3_xboole_0(k1_relat_1(esk3_0),esk2_0))&k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0)!=k1_funct_1(esk3_0,esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.12/0.37  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  fof(c_0_20, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.37  fof(c_0_21, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.37  fof(c_0_22, plain, ![X18, X19, X20, X21, X22]:k4_enumset1(X18,X18,X19,X20,X21,X22)=k3_enumset1(X18,X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.37  fof(c_0_23, plain, ![X23, X24, X25, X26, X27, X28]:k5_enumset1(X23,X23,X24,X25,X26,X27,X28)=k4_enumset1(X23,X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.37  fof(c_0_24, plain, ![X7, X8]:k2_tarski(X7,X8)=k2_tarski(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.12/0.37  fof(c_0_25, plain, ![X39, X40]:k5_relat_1(k6_relat_1(X40),k6_relat_1(X39))=k6_relat_1(k3_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_0,k3_xboole_0(k1_relat_1(esk3_0),esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_30, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_31, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  cnf(c_0_32, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  fof(c_0_33, plain, ![X31]:(k1_relat_1(k6_relat_1(X31))=X31&k2_relat_1(k6_relat_1(X31))=X31), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.12/0.37  cnf(c_0_34, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  fof(c_0_35, plain, ![X41, X42, X43]:(~v1_relat_1(X43)|~v1_funct_1(X43)|(~r2_hidden(X41,k1_relat_1(k7_relat_1(X43,X42)))|k1_funct_1(k7_relat_1(X43,X42),X41)=k1_funct_1(X43,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_0,k1_setfam_1(k5_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.12/0.37  cnf(c_0_37, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k5_enumset1(X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_19]), c_0_19]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 0.12/0.37  cnf(c_0_38, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_39, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0)!=k1_funct_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_41, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_44, plain, ![X32, X33, X34]:(((r2_hidden(X32,X33)|~r2_hidden(X32,k1_relat_1(k7_relat_1(X34,X33)))|~v1_relat_1(X34))&(r2_hidden(X32,k1_relat_1(X34))|~r2_hidden(X32,k1_relat_1(k7_relat_1(X34,X33)))|~v1_relat_1(X34)))&(~r2_hidden(X32,X33)|~r2_hidden(X32,k1_relat_1(X34))|r2_hidden(X32,k1_relat_1(k7_relat_1(X34,X33)))|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.12/0.37  fof(c_0_45, plain, ![X36, X37, X38]:(((r2_hidden(X36,k1_relat_1(X38))|~r2_hidden(X36,k1_relat_1(k5_relat_1(X38,k6_relat_1(X37))))|(~v1_relat_1(X38)|~v1_funct_1(X38)))&(r2_hidden(k1_funct_1(X38,X36),X37)|~r2_hidden(X36,k1_relat_1(k5_relat_1(X38,k6_relat_1(X37))))|(~v1_relat_1(X38)|~v1_funct_1(X38))))&(~r2_hidden(X36,k1_relat_1(X38))|~r2_hidden(k1_funct_1(X38,X36),X37)|r2_hidden(X36,k1_relat_1(k5_relat_1(X38,k6_relat_1(X37))))|(~v1_relat_1(X38)|~v1_funct_1(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_funct_1])])])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_0,k1_setfam_1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.12/0.37  cnf(c_0_47, plain, (k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.37  cnf(c_0_48, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_37]), c_0_39])).
% 0.12/0.37  fof(c_0_49, plain, ![X35]:(v1_relat_1(k6_relat_1(X35))&v1_funct_1(k6_relat_1(X35))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])])).
% 0.12/0.37  cnf(c_0_51, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.37  cnf(c_0_52, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k5_relat_1(X2,k6_relat_1(X3))))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (r2_hidden(esk1_0,k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(k1_relat_1(esk3_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.12/0.37  cnf(c_0_54, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.37  cnf(c_0_55, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(esk3_0))|~r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_43])])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_38]), c_0_54]), c_0_55])])).
% 0.12/0.37  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_48]), c_0_38]), c_0_54]), c_0_55])])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_53]), c_0_59]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 61
% 0.12/0.37  # Proof object clause steps            : 32
% 0.12/0.37  # Proof object formula steps           : 29
% 0.12/0.37  # Proof object conjectures             : 15
% 0.12/0.37  # Proof object clause conjectures      : 12
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 18
% 0.12/0.37  # Proof object initial formulas used   : 14
% 0.12/0.37  # Proof object generating inferences   : 7
% 0.12/0.37  # Proof object simplifying inferences  : 41
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 14
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 23
% 0.12/0.37  # Removed in clause preprocessing      : 6
% 0.12/0.37  # Initial clauses in saturation        : 17
% 0.12/0.37  # Processed clauses                    : 55
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 1
% 0.12/0.37  # ...remaining for further processing  : 52
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 4
% 0.12/0.37  # Generated clauses                    : 76
% 0.12/0.37  # ...of the previous two non-trivial   : 63
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 76
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 31
% 0.12/0.37  #    Positive orientable unit clauses  : 15
% 0.12/0.37  #    Positive unorientable unit clauses: 2
% 0.12/0.37  #    Negative unit clauses             : 3
% 0.12/0.37  #    Non-unit-clauses                  : 11
% 0.12/0.37  # Current number of unprocessed clauses: 42
% 0.12/0.37  # ...number of literals in the above   : 85
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 27
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 40
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 9
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.37  # Unit Clause-clause subsumption calls : 1
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 19
% 0.12/0.37  # BW rewrite match successes           : 19
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 2561
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.034 s
% 0.12/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
