%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 (1822 expanded)
%              Number of clauses        :   63 ( 807 expanded)
%              Number of leaves         :   22 ( 502 expanded)
%              Depth                    :   13
%              Number of atoms          :  164 (2575 expanded)
%              Number of equality atoms :   92 (1431 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t39_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(k3_subset_1(X1,X2),X2)
      <=> X2 = k2_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(c_0_22,plain,(
    ! [X37] : k2_subset_1(X37) = k3_subset_1(X37,k1_subset_1(X37)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_23,plain,(
    ! [X31] : k2_subset_1(X31) = X31 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_24,plain,(
    ! [X30] : k1_subset_1(X30) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_25,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | k3_subset_1(X35,k3_subset_1(X35,X36)) = X36 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_26,plain,(
    ! [X41] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X41)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_27,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X34] : m1_subset_1(k2_subset_1(X34),k1_zfmisc_1(X34)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_31,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | k3_subset_1(X32,X33) = k4_xboole_0(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_32,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_33,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_34,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_35,plain,(
    ! [X38,X39,X40] :
      ( ( ~ r1_tarski(X39,X40)
        | r1_tarski(k3_subset_1(X38,X40),k3_subset_1(X38,X39))
        | ~ m1_subset_1(X40,k1_zfmisc_1(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(X38)) )
      & ( ~ r1_tarski(k3_subset_1(X38,X40),k3_subset_1(X38,X39))
        | r1_tarski(X39,X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

cnf(c_0_36,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_41,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_28])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_49,plain,(
    ! [X17,X18,X19] : k5_xboole_0(k5_xboole_0(X17,X18),X19) = k5_xboole_0(X17,k5_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_50,plain,(
    ! [X20] : k5_xboole_0(X20,X20) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_51,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])])).

fof(c_0_54,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(k3_subset_1(X1,X2),X2)
        <=> X2 = k2_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t39_subset_1])).

fof(c_0_55,plain,(
    ! [X28,X29] : k3_tarski(k2_tarski(X28,X29)) = k2_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_56,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

fof(c_0_60,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & ( ~ r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)
      | esk2_0 != k2_subset_1(esk1_0) )
    & ( r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)
      | esk2_0 = k2_subset_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).

fof(c_0_61,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k3_xboole_0(X10,X11)) = X10 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_62,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_64,plain,(
    ! [X25,X26,X27] : k2_enumset1(X25,X25,X26,X27) = k1_enumset1(X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_65,plain,(
    ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X16,X15)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_37]),c_0_38])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_58]),c_0_67])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(esk1_0,esk2_0) = k3_subset_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_68])).

fof(c_0_76,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_77,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_78,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_70]),c_0_70]),c_0_42]),c_0_71]),c_0_71])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_66,c_0_73])).

fof(c_0_80,plain,(
    ! [X21,X22] : k2_xboole_0(X21,X22) = k5_xboole_0(X21,k4_xboole_0(X22,X21)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_subset_1(esk1_0,esk2_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)
    | esk2_0 != k2_subset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_83,plain,
    ( k3_subset_1(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_43]),c_0_58])).

cnf(c_0_84,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_68])).

cnf(c_0_86,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_52])).

cnf(c_0_87,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_44])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_subset_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_75])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k3_subset_1(X1,X2)) = k3_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_51])).

cnf(c_0_90,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_74]),c_0_67])).

cnf(c_0_92,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_subset_1(esk1_0,esk2_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_81]),c_0_67])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)
    | esk2_0 = k2_subset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_94,negated_conjecture,
    ( esk2_0 != esk1_0
    | ~ r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_28])).

cnf(c_0_95,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = k1_xboole_0
    | ~ r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_68])).

cnf(c_0_96,negated_conjecture,
    ( esk1_0 = esk2_0
    | ~ r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_97,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = X1
    | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_98,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk1_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_68])]),c_0_44])).

cnf(c_0_99,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_70]),c_0_42]),c_0_71])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_91])).

cnf(c_0_101,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk1_0) = k3_subset_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_92])).

cnf(c_0_102,negated_conjecture,
    ( esk2_0 = esk1_0
    | r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_93,c_0_28])).

cnf(c_0_103,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_48])]),c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( esk1_0 = esk2_0 ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99]),c_0_44]),c_0_98]),c_0_100]),c_0_101]),c_0_92]),c_0_100]),c_0_101]),c_0_102])).

cnf(c_0_106,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105]),c_0_106])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:08:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.52  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.52  #
% 0.20/0.52  # Preprocessing time       : 0.027 s
% 0.20/0.52  # Presaturation interreduction done
% 0.20/0.52  
% 0.20/0.52  # Proof found!
% 0.20/0.52  # SZS status Theorem
% 0.20/0.52  # SZS output start CNFRefutation
% 0.20/0.52  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.20/0.52  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.52  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.20/0.52  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.52  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.52  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.52  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.52  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.52  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.52  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.52  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 0.20/0.52  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.52  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.52  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.52  fof(t39_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 0.20/0.52  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.52  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.52  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.20/0.52  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.52  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.52  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.52  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.52  fof(c_0_22, plain, ![X37]:k2_subset_1(X37)=k3_subset_1(X37,k1_subset_1(X37)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.20/0.52  fof(c_0_23, plain, ![X31]:k2_subset_1(X31)=X31, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.52  fof(c_0_24, plain, ![X30]:k1_subset_1(X30)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.20/0.52  fof(c_0_25, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|k3_subset_1(X35,k3_subset_1(X35,X36))=X36), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.52  fof(c_0_26, plain, ![X41]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X41)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.52  cnf(c_0_27, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.52  cnf(c_0_28, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.52  cnf(c_0_29, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.52  fof(c_0_30, plain, ![X34]:m1_subset_1(k2_subset_1(X34),k1_zfmisc_1(X34)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.52  fof(c_0_31, plain, ![X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(X32))|k3_subset_1(X32,X33)=k4_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.52  fof(c_0_32, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.52  fof(c_0_33, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.52  fof(c_0_34, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.52  fof(c_0_35, plain, ![X38, X39, X40]:((~r1_tarski(X39,X40)|r1_tarski(k3_subset_1(X38,X40),k3_subset_1(X38,X39))|~m1_subset_1(X40,k1_zfmisc_1(X38))|~m1_subset_1(X39,k1_zfmisc_1(X38)))&(~r1_tarski(k3_subset_1(X38,X40),k3_subset_1(X38,X39))|r1_tarski(X39,X40)|~m1_subset_1(X40,k1_zfmisc_1(X38))|~m1_subset_1(X39,k1_zfmisc_1(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 0.20/0.52  cnf(c_0_36, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.52  cnf(c_0_37, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.52  cnf(c_0_38, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.20/0.52  cnf(c_0_39, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.52  fof(c_0_40, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.52  cnf(c_0_41, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.52  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.52  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.52  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.52  cnf(c_0_45, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.52  cnf(c_0_46, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.20/0.52  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_39, c_0_28])).
% 0.20/0.52  cnf(c_0_48, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.52  fof(c_0_49, plain, ![X17, X18, X19]:k5_xboole_0(k5_xboole_0(X17,X18),X19)=k5_xboole_0(X17,k5_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.52  fof(c_0_50, plain, ![X20]:k5_xboole_0(X20,X20)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.52  cnf(c_0_51, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.52  cnf(c_0_52, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.52  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])])).
% 0.20/0.52  fof(c_0_54, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1)))), inference(assume_negation,[status(cth)],[t39_subset_1])).
% 0.20/0.52  fof(c_0_55, plain, ![X28, X29]:k3_tarski(k2_tarski(X28,X29))=k2_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.52  fof(c_0_56, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.52  cnf(c_0_57, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.52  cnf(c_0_58, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.52  cnf(c_0_59, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.20/0.52  fof(c_0_60, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&((~r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)|esk2_0!=k2_subset_1(esk1_0))&(r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)|esk2_0=k2_subset_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).
% 0.20/0.52  fof(c_0_61, plain, ![X10, X11]:k2_xboole_0(X10,k3_xboole_0(X10,X11))=X10, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.20/0.52  cnf(c_0_62, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.52  cnf(c_0_63, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.52  fof(c_0_64, plain, ![X25, X26, X27]:k2_enumset1(X25,X25,X26,X27)=k1_enumset1(X25,X26,X27), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.52  fof(c_0_65, plain, ![X15, X16]:k2_xboole_0(X15,k4_xboole_0(X16,X15))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.52  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.52  cnf(c_0_67, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_37]), c_0_38])).
% 0.20/0.52  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.52  cnf(c_0_69, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.52  cnf(c_0_70, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.52  cnf(c_0_71, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.52  cnf(c_0_72, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.52  cnf(c_0_73, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_58]), c_0_67])).
% 0.20/0.52  cnf(c_0_74, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_57])).
% 0.20/0.52  cnf(c_0_75, negated_conjecture, (k5_xboole_0(esk1_0,esk2_0)=k3_subset_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_59, c_0_68])).
% 0.20/0.52  fof(c_0_76, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.52  cnf(c_0_77, plain, (k3_tarski(k2_enumset1(X1,X1,X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.20/0.52  cnf(c_0_78, plain, (k3_tarski(k2_enumset1(X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_70]), c_0_70]), c_0_42]), c_0_71]), c_0_71])).
% 0.20/0.52  cnf(c_0_79, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_66, c_0_73])).
% 0.20/0.52  fof(c_0_80, plain, ![X21, X22]:k2_xboole_0(X21,X22)=k5_xboole_0(X21,k4_xboole_0(X22,X21)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.52  cnf(c_0_81, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_subset_1(esk1_0,esk2_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.52  cnf(c_0_82, negated_conjecture, (~r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)|esk2_0!=k2_subset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.52  cnf(c_0_83, plain, (k3_subset_1(X1,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_43]), c_0_58])).
% 0.20/0.52  cnf(c_0_84, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.52  cnf(c_0_85, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_53, c_0_68])).
% 0.20/0.52  cnf(c_0_86, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_77, c_0_52])).
% 0.20/0.52  cnf(c_0_87, plain, (k3_tarski(k2_enumset1(X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))=k3_tarski(k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_78, c_0_44])).
% 0.20/0.52  cnf(c_0_88, negated_conjecture, (k5_xboole_0(esk1_0,k3_subset_1(esk1_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_79, c_0_75])).
% 0.20/0.52  cnf(c_0_89, plain, (k5_xboole_0(X1,k3_subset_1(X1,X2))=k3_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_79, c_0_51])).
% 0.20/0.52  cnf(c_0_90, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.52  cnf(c_0_91, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_74]), c_0_67])).
% 0.20/0.52  cnf(c_0_92, negated_conjecture, (k5_xboole_0(esk2_0,k3_subset_1(esk1_0,esk2_0))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_81]), c_0_67])).
% 0.20/0.52  cnf(c_0_93, negated_conjecture, (r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)|esk2_0=k2_subset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.52  cnf(c_0_94, negated_conjecture, (esk2_0!=esk1_0|~r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[c_0_82, c_0_28])).
% 0.20/0.52  cnf(c_0_95, negated_conjecture, (k3_subset_1(esk1_0,esk2_0)=k1_xboole_0|~r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_83, c_0_68])).
% 0.20/0.52  cnf(c_0_96, negated_conjecture, (esk1_0=esk2_0|~r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.52  cnf(c_0_97, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=X1|~r1_tarski(k5_xboole_0(X2,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.52  cnf(c_0_98, negated_conjecture, (k3_xboole_0(esk2_0,esk1_0)=esk2_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_68])]), c_0_44])).
% 0.20/0.52  cnf(c_0_99, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_70]), c_0_42]), c_0_71])).
% 0.20/0.52  cnf(c_0_100, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_79, c_0_91])).
% 0.20/0.52  cnf(c_0_101, negated_conjecture, (k5_xboole_0(esk2_0,esk1_0)=k3_subset_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_79, c_0_92])).
% 0.20/0.52  cnf(c_0_102, negated_conjecture, (esk2_0=esk1_0|r1_tarski(k3_subset_1(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[c_0_93, c_0_28])).
% 0.20/0.52  cnf(c_0_103, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.52  cnf(c_0_104, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_48])]), c_0_96])).
% 0.20/0.52  cnf(c_0_105, negated_conjecture, (esk1_0=esk2_0), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99]), c_0_44]), c_0_98]), c_0_100]), c_0_101]), c_0_92]), c_0_100]), c_0_101]), c_0_102])).
% 0.20/0.52  cnf(c_0_106, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_103])).
% 0.20/0.52  cnf(c_0_107, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105]), c_0_106])]), ['proof']).
% 0.20/0.52  # SZS output end CNFRefutation
% 0.20/0.52  # Proof object total steps             : 108
% 0.20/0.52  # Proof object clause steps            : 63
% 0.20/0.52  # Proof object formula steps           : 45
% 0.20/0.52  # Proof object conjectures             : 20
% 0.20/0.52  # Proof object clause conjectures      : 17
% 0.20/0.52  # Proof object formula conjectures     : 3
% 0.20/0.52  # Proof object initial clauses used    : 25
% 0.20/0.52  # Proof object initial formulas used   : 22
% 0.20/0.52  # Proof object generating inferences   : 26
% 0.20/0.52  # Proof object simplifying inferences  : 47
% 0.20/0.52  # Training examples: 0 positive, 0 negative
% 0.20/0.52  # Parsed axioms                        : 22
% 0.20/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.52  # Initial clauses                      : 27
% 0.20/0.52  # Removed in clause preprocessing      : 6
% 0.20/0.52  # Initial clauses in saturation        : 21
% 0.20/0.52  # Processed clauses                    : 1437
% 0.20/0.52  # ...of these trivial                  : 41
% 0.20/0.52  # ...subsumed                          : 1077
% 0.20/0.52  # ...remaining for further processing  : 319
% 0.20/0.52  # Other redundant clauses eliminated   : 2
% 0.20/0.52  # Clauses deleted for lack of memory   : 0
% 0.20/0.52  # Backward-subsumed                    : 18
% 0.20/0.52  # Backward-rewritten                   : 152
% 0.20/0.52  # Generated clauses                    : 9752
% 0.20/0.52  # ...of the previous two non-trivial   : 9058
% 0.20/0.52  # Contextual simplify-reflections      : 22
% 0.20/0.52  # Paramodulations                      : 9750
% 0.20/0.52  # Factorizations                       : 0
% 0.20/0.52  # Equation resolutions                 : 2
% 0.20/0.52  # Propositional unsat checks           : 0
% 0.20/0.52  #    Propositional check models        : 0
% 0.20/0.52  #    Propositional check unsatisfiable : 0
% 0.20/0.52  #    Propositional clauses             : 0
% 0.20/0.52  #    Propositional clauses after purity: 0
% 0.20/0.52  #    Propositional unsat core size     : 0
% 0.20/0.52  #    Propositional preprocessing time  : 0.000
% 0.20/0.52  #    Propositional encoding time       : 0.000
% 0.20/0.52  #    Propositional solver time         : 0.000
% 0.20/0.52  #    Success case prop preproc time    : 0.000
% 0.20/0.52  #    Success case prop encoding time   : 0.000
% 0.20/0.52  #    Success case prop solver time     : 0.000
% 0.20/0.52  # Current number of processed clauses  : 127
% 0.20/0.52  #    Positive orientable unit clauses  : 25
% 0.20/0.52  #    Positive unorientable unit clauses: 10
% 0.20/0.52  #    Negative unit clauses             : 0
% 0.20/0.52  #    Non-unit-clauses                  : 92
% 0.20/0.52  # Current number of unprocessed clauses: 7486
% 0.20/0.52  # ...number of literals in the above   : 19990
% 0.20/0.52  # Current number of archived formulas  : 0
% 0.20/0.52  # Current number of archived clauses   : 196
% 0.20/0.52  # Clause-clause subsumption calls (NU) : 9469
% 0.20/0.52  # Rec. Clause-clause subsumption calls : 6385
% 0.20/0.52  # Non-unit clause-clause subsumptions  : 902
% 0.20/0.52  # Unit Clause-clause subsumption calls : 166
% 0.20/0.52  # Rewrite failures with RHS unbound    : 0
% 0.20/0.52  # BW rewrite match attempts            : 264
% 0.20/0.52  # BW rewrite match successes           : 178
% 0.20/0.52  # Condensation attempts                : 0
% 0.20/0.52  # Condensation successes               : 0
% 0.20/0.52  # Termbank termtop insertions          : 146163
% 0.20/0.52  
% 0.20/0.52  # -------------------------------------------------
% 0.20/0.52  # User time                : 0.173 s
% 0.20/0.52  # System time              : 0.009 s
% 0.20/0.52  # Total time               : 0.182 s
% 0.20/0.52  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
