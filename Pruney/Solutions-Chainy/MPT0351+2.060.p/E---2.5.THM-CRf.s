%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:34 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 167 expanded)
%              Number of clauses        :   40 (  73 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  136 ( 271 expanded)
%              Number of equality atoms :   62 ( 137 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(commutativity_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k4_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t28_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k2_subset_1(X1)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(c_0_17,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | ~ m1_subset_1(X30,k1_zfmisc_1(X28))
      | k4_subset_1(X28,X29,X30) = k4_subset_1(X28,X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).

fof(c_0_18,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X32,X31)
        | r2_hidden(X32,X31)
        | v1_xboole_0(X31) )
      & ( ~ r2_hidden(X32,X31)
        | m1_subset_1(X32,X31)
        | v1_xboole_0(X31) )
      & ( ~ m1_subset_1(X32,X31)
        | v1_xboole_0(X32)
        | ~ v1_xboole_0(X31) )
      & ( ~ v1_xboole_0(X32)
        | m1_subset_1(X32,X31)
        | ~ v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_19,plain,(
    ! [X35] : ~ v1_xboole_0(k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k2_subset_1(X1)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t28_subset_1])).

fof(c_0_21,plain,(
    ! [X34] : m1_subset_1(k2_subset_1(X34),k1_zfmisc_1(X34)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_22,plain,(
    ! [X33] : k2_subset_1(X33) = X33 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_23,plain,(
    ! [X26,X27] : k3_tarski(k2_tarski(X26,X27)) = k2_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_25,plain,
    ( k4_subset_1(X2,X1,X3) = k4_subset_1(X2,X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & k4_subset_1(esk2_0,esk3_0,k2_subset_1(esk2_0)) != k2_subset_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | ~ m1_subset_1(X38,k1_zfmisc_1(X36))
      | k4_subset_1(X36,X37,X38) = k2_xboole_0(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_32,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_35,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X21,X20)
        | r1_tarski(X21,X19)
        | X20 != k1_zfmisc_1(X19) )
      & ( ~ r1_tarski(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k1_zfmisc_1(X19) )
      & ( ~ r2_hidden(esk1_2(X23,X24),X24)
        | ~ r1_tarski(esk1_2(X23,X24),X23)
        | X24 = k1_zfmisc_1(X23) )
      & ( r2_hidden(esk1_2(X23,X24),X24)
        | r1_tarski(esk1_2(X23,X24),X23)
        | X24 = k1_zfmisc_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_36,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X1,X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X3,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_43,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k3_xboole_0(X8,X9) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_45,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k2_xboole_0(X12,X13)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_46,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_47,plain,(
    ! [X7] : k2_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_48,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k2_subset_1(esk2_0)) != k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_49,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,X1) = k4_subset_1(esk2_0,X1,esk3_0)
    | ~ r2_hidden(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_27])).

cnf(c_0_51,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_enumset1(X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

fof(c_0_52,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X11,X10)) = k2_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_58,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = X4 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_59,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,esk2_0) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_30]),c_0_30])).

cnf(c_0_60,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,esk2_0) = k4_subset_1(esk2_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( k4_subset_1(esk2_0,X1,esk3_0) = k3_tarski(k2_enumset1(X1,X1,X1,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_37])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_27])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_41]),c_0_56]),c_0_42])).

cnf(c_0_66,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_41]),c_0_42])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( k4_subset_1(esk2_0,esk2_0,esk3_0) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( k4_subset_1(esk2_0,esk2_0,esk3_0) = k3_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_39])).

cnf(c_0_70,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_41]),c_0_41]),c_0_56]),c_0_42]),c_0_42])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( k3_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_66]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:36:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  # Version: 2.5pre002
% 0.14/0.37  # No SInE strategy applied
% 0.14/0.37  # Trying AutoSched0 for 299 seconds
% 0.22/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.22/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.22/0.39  #
% 0.22/0.39  # Preprocessing time       : 0.018 s
% 0.22/0.39  # Presaturation interreduction done
% 0.22/0.39  
% 0.22/0.39  # Proof found!
% 0.22/0.39  # SZS status Theorem
% 0.22/0.39  # SZS output start CNFRefutation
% 0.22/0.39  fof(commutativity_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k4_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 0.22/0.39  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.22/0.39  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.22/0.39  fof(t28_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k2_subset_1(X1))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 0.22/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.22/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.22/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.22/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.22/0.39  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.22/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.22/0.39  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.22/0.39  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.22/0.39  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.22/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.22/0.39  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.22/0.39  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.22/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.22/0.39  fof(c_0_17, plain, ![X28, X29, X30]:(~m1_subset_1(X29,k1_zfmisc_1(X28))|~m1_subset_1(X30,k1_zfmisc_1(X28))|k4_subset_1(X28,X29,X30)=k4_subset_1(X28,X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).
% 0.22/0.39  fof(c_0_18, plain, ![X31, X32]:(((~m1_subset_1(X32,X31)|r2_hidden(X32,X31)|v1_xboole_0(X31))&(~r2_hidden(X32,X31)|m1_subset_1(X32,X31)|v1_xboole_0(X31)))&((~m1_subset_1(X32,X31)|v1_xboole_0(X32)|~v1_xboole_0(X31))&(~v1_xboole_0(X32)|m1_subset_1(X32,X31)|~v1_xboole_0(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.22/0.39  fof(c_0_19, plain, ![X35]:~v1_xboole_0(k1_zfmisc_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.22/0.39  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k2_subset_1(X1))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t28_subset_1])).
% 0.22/0.39  fof(c_0_21, plain, ![X34]:m1_subset_1(k2_subset_1(X34),k1_zfmisc_1(X34)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.22/0.39  fof(c_0_22, plain, ![X33]:k2_subset_1(X33)=X33, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.22/0.39  fof(c_0_23, plain, ![X26, X27]:k3_tarski(k2_tarski(X26,X27))=k2_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.22/0.39  fof(c_0_24, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.22/0.39  cnf(c_0_25, plain, (k4_subset_1(X2,X1,X3)=k4_subset_1(X2,X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.22/0.39  cnf(c_0_26, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.22/0.39  cnf(c_0_27, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.22/0.39  fof(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&k4_subset_1(esk2_0,esk3_0,k2_subset_1(esk2_0))!=k2_subset_1(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.22/0.39  cnf(c_0_29, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.22/0.39  cnf(c_0_30, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.22/0.39  fof(c_0_31, plain, ![X36, X37, X38]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|~m1_subset_1(X38,k1_zfmisc_1(X36))|k4_subset_1(X36,X37,X38)=k2_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.22/0.39  cnf(c_0_32, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.22/0.39  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.22/0.39  fof(c_0_34, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.22/0.39  fof(c_0_35, plain, ![X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X21,X20)|r1_tarski(X21,X19)|X20!=k1_zfmisc_1(X19))&(~r1_tarski(X22,X19)|r2_hidden(X22,X20)|X20!=k1_zfmisc_1(X19)))&((~r2_hidden(esk1_2(X23,X24),X24)|~r1_tarski(esk1_2(X23,X24),X23)|X24=k1_zfmisc_1(X23))&(r2_hidden(esk1_2(X23,X24),X24)|r1_tarski(esk1_2(X23,X24),X23)|X24=k1_zfmisc_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.22/0.39  cnf(c_0_36, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X1,X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r2_hidden(X3,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.22/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.22/0.39  cnf(c_0_38, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.22/0.39  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.22/0.39  cnf(c_0_40, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.22/0.39  cnf(c_0_41, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.22/0.39  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.22/0.39  fof(c_0_43, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k3_xboole_0(X8,X9)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.22/0.39  cnf(c_0_44, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.22/0.39  fof(c_0_45, plain, ![X12, X13]:k4_xboole_0(X12,k2_xboole_0(X12,X13))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.22/0.39  fof(c_0_46, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.22/0.39  fof(c_0_47, plain, ![X7]:k2_xboole_0(X7,k1_xboole_0)=X7, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.22/0.39  cnf(c_0_48, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k2_subset_1(esk2_0))!=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.22/0.39  cnf(c_0_49, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,X1)=k4_subset_1(esk2_0,X1,esk3_0)|~r2_hidden(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.22/0.39  cnf(c_0_50, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_27])).
% 0.22/0.39  cnf(c_0_51, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_enumset1(X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.22/0.39  fof(c_0_52, plain, ![X10, X11]:k2_xboole_0(X10,k4_xboole_0(X11,X10))=k2_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.22/0.39  cnf(c_0_53, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.22/0.39  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_44])).
% 0.22/0.39  cnf(c_0_55, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.22/0.39  cnf(c_0_56, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.22/0.39  cnf(c_0_57, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.22/0.39  fof(c_0_58, plain, ![X4]:k3_xboole_0(X4,X4)=X4, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.22/0.39  cnf(c_0_59, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,esk2_0)!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_30]), c_0_30])).
% 0.22/0.39  cnf(c_0_60, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,esk2_0)=k4_subset_1(esk2_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.22/0.39  cnf(c_0_61, negated_conjecture, (k4_subset_1(esk2_0,X1,esk3_0)=k3_tarski(k2_enumset1(X1,X1,X1,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_51, c_0_37])).
% 0.22/0.39  cnf(c_0_62, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.22/0.39  cnf(c_0_63, plain, (k3_xboole_0(X1,X2)=X1|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.22/0.39  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_37]), c_0_27])).
% 0.22/0.39  cnf(c_0_65, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_41]), c_0_56]), c_0_42])).
% 0.22/0.39  cnf(c_0_66, plain, (k3_tarski(k2_enumset1(X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_41]), c_0_42])).
% 0.22/0.39  cnf(c_0_67, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.22/0.39  cnf(c_0_68, negated_conjecture, (k4_subset_1(esk2_0,esk2_0,esk3_0)!=esk2_0), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.22/0.39  cnf(c_0_69, negated_conjecture, (k4_subset_1(esk2_0,esk2_0,esk3_0)=k3_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_61, c_0_39])).
% 0.22/0.39  cnf(c_0_70, plain, (k3_tarski(k2_enumset1(X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_41]), c_0_41]), c_0_56]), c_0_42]), c_0_42])).
% 0.22/0.39  cnf(c_0_71, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.22/0.39  cnf(c_0_72, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.22/0.39  cnf(c_0_73, negated_conjecture, (k3_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.22/0.39  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_66]), c_0_73]), ['proof']).
% 0.22/0.39  # SZS output end CNFRefutation
% 0.22/0.39  # Proof object total steps             : 75
% 0.22/0.39  # Proof object clause steps            : 40
% 0.22/0.39  # Proof object formula steps           : 35
% 0.22/0.39  # Proof object conjectures             : 15
% 0.22/0.39  # Proof object clause conjectures      : 12
% 0.22/0.39  # Proof object formula conjectures     : 3
% 0.22/0.39  # Proof object initial clauses used    : 19
% 0.22/0.39  # Proof object initial formulas used   : 17
% 0.22/0.39  # Proof object generating inferences   : 11
% 0.22/0.39  # Proof object simplifying inferences  : 26
% 0.22/0.39  # Training examples: 0 positive, 0 negative
% 0.22/0.39  # Parsed axioms                        : 17
% 0.22/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.39  # Initial clauses                      : 24
% 0.22/0.39  # Removed in clause preprocessing      : 5
% 0.22/0.39  # Initial clauses in saturation        : 19
% 0.22/0.39  # Processed clauses                    : 88
% 0.22/0.39  # ...of these trivial                  : 3
% 0.22/0.39  # ...subsumed                          : 14
% 0.22/0.39  # ...remaining for further processing  : 70
% 0.22/0.39  # Other redundant clauses eliminated   : 2
% 0.22/0.39  # Clauses deleted for lack of memory   : 0
% 0.22/0.39  # Backward-subsumed                    : 0
% 0.22/0.39  # Backward-rewritten                   : 3
% 0.22/0.39  # Generated clauses                    : 84
% 0.22/0.39  # ...of the previous two non-trivial   : 59
% 0.22/0.39  # Contextual simplify-reflections      : 0
% 0.22/0.39  # Paramodulations                      : 82
% 0.22/0.39  # Factorizations                       : 0
% 0.22/0.39  # Equation resolutions                 : 2
% 0.22/0.39  # Propositional unsat checks           : 0
% 0.22/0.39  #    Propositional check models        : 0
% 0.22/0.39  #    Propositional check unsatisfiable : 0
% 0.22/0.39  #    Propositional clauses             : 0
% 0.22/0.39  #    Propositional clauses after purity: 0
% 0.22/0.39  #    Propositional unsat core size     : 0
% 0.22/0.39  #    Propositional preprocessing time  : 0.000
% 0.22/0.39  #    Propositional encoding time       : 0.000
% 0.22/0.39  #    Propositional solver time         : 0.000
% 0.22/0.39  #    Success case prop preproc time    : 0.000
% 0.22/0.39  #    Success case prop encoding time   : 0.000
% 0.22/0.39  #    Success case prop solver time     : 0.000
% 0.22/0.39  # Current number of processed clauses  : 46
% 0.22/0.39  #    Positive orientable unit clauses  : 18
% 0.22/0.39  #    Positive unorientable unit clauses: 0
% 0.22/0.39  #    Negative unit clauses             : 2
% 0.22/0.39  #    Non-unit-clauses                  : 26
% 0.22/0.39  # Current number of unprocessed clauses: 9
% 0.22/0.39  # ...number of literals in the above   : 21
% 0.22/0.39  # Current number of archived formulas  : 0
% 0.22/0.39  # Current number of archived clauses   : 27
% 0.22/0.39  # Clause-clause subsumption calls (NU) : 99
% 0.22/0.39  # Rec. Clause-clause subsumption calls : 99
% 0.22/0.39  # Non-unit clause-clause subsumptions  : 6
% 0.22/0.39  # Unit Clause-clause subsumption calls : 29
% 0.22/0.39  # Rewrite failures with RHS unbound    : 0
% 0.22/0.39  # BW rewrite match attempts            : 33
% 0.22/0.39  # BW rewrite match successes           : 2
% 0.22/0.39  # Condensation attempts                : 0
% 0.22/0.39  # Condensation successes               : 0
% 0.22/0.39  # Termbank termtop insertions          : 2533
% 0.22/0.39  
% 0.22/0.39  # -------------------------------------------------
% 0.22/0.39  # User time                : 0.022 s
% 0.22/0.39  # System time              : 0.002 s
% 0.22/0.39  # Total time               : 0.024 s
% 0.22/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
