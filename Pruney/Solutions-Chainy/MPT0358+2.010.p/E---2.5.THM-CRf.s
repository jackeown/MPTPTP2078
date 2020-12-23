%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:51 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 477 expanded)
%              Number of clauses        :   59 ( 225 expanded)
%              Number of leaves         :   14 ( 122 expanded)
%              Depth                    :   15
%              Number of atoms          :  188 ( 858 expanded)
%              Number of equality atoms :   81 ( 452 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(c_0_14,plain,(
    ! [X15,X16,X17] : k5_xboole_0(k5_xboole_0(X15,X16),X17) = k5_xboole_0(X15,k5_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_15,plain,(
    ! [X18] : k5_xboole_0(X18,X18) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_16,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_17,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k3_xboole_0(X10,X11) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_19,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_20,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X14] : k5_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_23,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_28])).

cnf(c_0_32,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_27,c_0_31])).

fof(c_0_34,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

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
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k5_xboole_0(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_37,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X29))
      | k3_subset_1(X29,X30) = k4_xboole_0(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_29])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_43,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X27,X26)
        | r2_hidden(X27,X26)
        | v1_xboole_0(X26) )
      & ( ~ r2_hidden(X27,X26)
        | m1_subset_1(X27,X26)
        | v1_xboole_0(X26) )
      & ( ~ m1_subset_1(X27,X26)
        | v1_xboole_0(X27)
        | ~ v1_xboole_0(X26) )
      & ( ~ v1_xboole_0(X27)
        | m1_subset_1(X27,X26)
        | ~ v1_xboole_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_21])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),X3)
    | X3 != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k5_xboole_0(X1,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_32])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_42]),c_0_28])).

cnf(c_0_52,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_54,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0))
      | esk3_0 != k1_subset_1(esk2_0) )
    & ( r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0))
      | esk3_0 = k1_subset_1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

fof(c_0_55,plain,(
    ! [X31] : ~ v1_xboole_0(k1_zfmisc_1(X31)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | X4 != k1_zfmisc_1(X3)
    | X4 != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r1_tarski(k5_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k3_subset_1(X1,X2)) = k3_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_52])).

cnf(c_0_60,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_52])).

fof(c_0_61,plain,(
    ! [X28] : k1_subset_1(X28) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | X1 != k1_zfmisc_1(X3)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_56])).

cnf(c_0_66,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_67,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_xboole_0(X1,X2),k3_subset_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0))
    | esk3_0 = k1_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_69,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | k1_zfmisc_1(esk2_0) != k1_zfmisc_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k3_subset_1(X1,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_30])).

cnf(c_0_73,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0))
    | esk3_0 != k1_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_26])).

cnf(c_0_77,plain,
    ( k1_xboole_0 = X1
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_71])).

cnf(c_0_78,plain,
    ( k3_subset_1(X1,X2) = k5_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_30])).

cnf(c_0_79,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_63]),c_0_74])])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_51])).

cnf(c_0_81,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_69])).

cnf(c_0_82,plain,
    ( k3_subset_1(X1,X2) = X1
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_71]),c_0_28])).

cnf(c_0_83,plain,
    ( k1_xboole_0 = X1
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_47])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk2_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_63]),c_0_74])])).

cnf(c_0_85,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_74]),c_0_63])]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_84]),c_0_21])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:17:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 3.04/3.25  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 3.04/3.25  # and selection function SelectMaxLComplexAvoidPosPred.
% 3.04/3.25  #
% 3.04/3.25  # Preprocessing time       : 0.027 s
% 3.04/3.25  
% 3.04/3.25  # Proof found!
% 3.04/3.25  # SZS status Theorem
% 3.04/3.25  # SZS output start CNFRefutation
% 3.04/3.25  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.04/3.25  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.04/3.25  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.04/3.25  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.04/3.25  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.04/3.25  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.04/3.25  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.04/3.25  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.04/3.25  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.04/3.25  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.04/3.25  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.04/3.25  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.04/3.25  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.04/3.25  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.04/3.25  fof(c_0_14, plain, ![X15, X16, X17]:k5_xboole_0(k5_xboole_0(X15,X16),X17)=k5_xboole_0(X15,k5_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 3.04/3.25  fof(c_0_15, plain, ![X18]:k5_xboole_0(X18,X18)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 3.04/3.25  fof(c_0_16, plain, ![X12, X13]:r1_tarski(k4_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 3.04/3.25  fof(c_0_17, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 3.04/3.25  fof(c_0_18, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k3_xboole_0(X10,X11)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 3.04/3.25  fof(c_0_19, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 3.04/3.25  cnf(c_0_20, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.04/3.25  cnf(c_0_21, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.04/3.25  fof(c_0_22, plain, ![X14]:k5_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t5_boole])).
% 3.04/3.25  cnf(c_0_23, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.04/3.25  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.04/3.25  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.04/3.25  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.04/3.25  cnf(c_0_27, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 3.04/3.25  cnf(c_0_28, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.04/3.25  cnf(c_0_29, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 3.04/3.25  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 3.04/3.25  cnf(c_0_31, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_28])).
% 3.04/3.25  cnf(c_0_32, plain, (r1_tarski(k5_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 3.04/3.25  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_27, c_0_31])).
% 3.04/3.25  fof(c_0_34, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.04/3.25  fof(c_0_35, plain, ![X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X21,X20)|r1_tarski(X21,X19)|X20!=k1_zfmisc_1(X19))&(~r1_tarski(X22,X19)|r2_hidden(X22,X20)|X20!=k1_zfmisc_1(X19)))&((~r2_hidden(esk1_2(X23,X24),X24)|~r1_tarski(esk1_2(X23,X24),X23)|X24=k1_zfmisc_1(X23))&(r2_hidden(esk1_2(X23,X24),X24)|r1_tarski(esk1_2(X23,X24),X23)|X24=k1_zfmisc_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 3.04/3.25  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r1_tarski(k5_xboole_0(X2,X1),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 3.04/3.25  fof(c_0_37, plain, ![X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(X29))|k3_subset_1(X29,X30)=k4_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 3.04/3.25  cnf(c_0_38, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.04/3.25  cnf(c_0_39, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 3.04/3.25  cnf(c_0_40, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_36, c_0_29])).
% 3.04/3.25  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.04/3.25  cnf(c_0_42, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 3.04/3.25  cnf(c_0_43, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 3.04/3.25  fof(c_0_44, plain, ![X26, X27]:(((~m1_subset_1(X27,X26)|r2_hidden(X27,X26)|v1_xboole_0(X26))&(~r2_hidden(X27,X26)|m1_subset_1(X27,X26)|v1_xboole_0(X26)))&((~m1_subset_1(X27,X26)|v1_xboole_0(X27)|~v1_xboole_0(X26))&(~v1_xboole_0(X27)|m1_subset_1(X27,X26)|~v1_xboole_0(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 3.04/3.25  fof(c_0_45, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 3.04/3.25  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_25]), c_0_21])).
% 3.04/3.25  cnf(c_0_47, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_38])).
% 3.04/3.25  cnf(c_0_48, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 3.04/3.25  cnf(c_0_49, plain, (r2_hidden(k3_xboole_0(X1,X2),X3)|X3!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 3.04/3.25  cnf(c_0_50, plain, (k5_xboole_0(X1,X2)=X1|~r1_tarski(X1,k5_xboole_0(X1,X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_32])).
% 3.04/3.25  cnf(c_0_51, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_42]), c_0_28])).
% 3.04/3.25  cnf(c_0_52, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_43, c_0_24])).
% 3.04/3.25  cnf(c_0_53, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 3.04/3.25  fof(c_0_54, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0))|esk3_0!=k1_subset_1(esk2_0))&(r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0))|esk3_0=k1_subset_1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).
% 3.04/3.25  fof(c_0_55, plain, ![X31]:~v1_xboole_0(k1_zfmisc_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 3.04/3.25  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 3.04/3.25  cnf(c_0_57, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|X4!=k1_zfmisc_1(X3)|X4!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 3.04/3.25  cnf(c_0_58, plain, (X1=X2|~r1_tarski(k5_xboole_0(X1,X2),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 3.04/3.25  cnf(c_0_59, plain, (k5_xboole_0(X1,k3_subset_1(X1,X2))=k3_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_52])).
% 3.04/3.25  cnf(c_0_60, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_52])).
% 3.04/3.25  fof(c_0_61, plain, ![X28]:k1_subset_1(X28)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 3.04/3.25  cnf(c_0_62, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|X1!=k1_zfmisc_1(X3)|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_48, c_0_53])).
% 3.04/3.25  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 3.04/3.25  cnf(c_0_64, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 3.04/3.25  cnf(c_0_65, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_56])).
% 3.04/3.25  cnf(c_0_66, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|k1_zfmisc_1(X3)!=k1_zfmisc_1(X1)), inference(er,[status(thm)],[c_0_57])).
% 3.04/3.25  cnf(c_0_67, plain, (k3_subset_1(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k3_xboole_0(X1,X2),k3_subset_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 3.04/3.25  cnf(c_0_68, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0))|esk3_0=k1_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 3.04/3.25  cnf(c_0_69, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_61])).
% 3.04/3.25  cnf(c_0_70, negated_conjecture, (r1_tarski(esk3_0,X1)|k1_zfmisc_1(esk2_0)!=k1_zfmisc_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 3.04/3.25  cnf(c_0_71, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k1_zfmisc_1(k1_xboole_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 3.04/3.25  cnf(c_0_72, plain, (k3_subset_1(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,k3_subset_1(X1,X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_67, c_0_30])).
% 3.04/3.25  cnf(c_0_73, negated_conjecture, (esk3_0=k1_xboole_0|r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 3.04/3.25  cnf(c_0_74, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(er,[status(thm)],[c_0_70])).
% 3.04/3.25  cnf(c_0_75, negated_conjecture, (~r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0))|esk3_0!=k1_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 3.04/3.25  cnf(c_0_76, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_52, c_0_26])).
% 3.04/3.25  cnf(c_0_77, plain, (k1_xboole_0=X1|k1_zfmisc_1(k1_xboole_0)!=k1_zfmisc_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_71])).
% 3.04/3.25  cnf(c_0_78, plain, (k3_subset_1(X1,X2)=k5_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_52, c_0_30])).
% 3.04/3.25  cnf(c_0_79, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_63]), c_0_74])])).
% 3.04/3.25  cnf(c_0_80, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_51])).
% 3.04/3.25  cnf(c_0_81, negated_conjecture, (esk3_0!=k1_xboole_0|~r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_75, c_0_69])).
% 3.04/3.25  cnf(c_0_82, plain, (k3_subset_1(X1,X2)=X1|k1_zfmisc_1(k1_xboole_0)!=k1_zfmisc_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_71]), c_0_28])).
% 3.04/3.25  cnf(c_0_83, plain, (k1_xboole_0=X1|k1_zfmisc_1(k1_xboole_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_77, c_0_47])).
% 3.04/3.25  cnf(c_0_84, negated_conjecture, (k5_xboole_0(esk3_0,esk2_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_63]), c_0_74])])).
% 3.04/3.25  cnf(c_0_85, negated_conjecture, (k1_zfmisc_1(esk3_0)!=k1_zfmisc_1(k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_74]), c_0_63])]), c_0_83])).
% 3.04/3.25  cnf(c_0_86, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_84]), c_0_21])])).
% 3.04/3.25  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])]), ['proof']).
% 3.04/3.25  # SZS output end CNFRefutation
% 3.04/3.25  # Proof object total steps             : 88
% 3.04/3.25  # Proof object clause steps            : 59
% 3.04/3.25  # Proof object formula steps           : 29
% 3.04/3.25  # Proof object conjectures             : 15
% 3.04/3.25  # Proof object clause conjectures      : 12
% 3.04/3.25  # Proof object formula conjectures     : 3
% 3.04/3.25  # Proof object initial clauses used    : 18
% 3.04/3.25  # Proof object initial formulas used   : 14
% 3.04/3.25  # Proof object generating inferences   : 34
% 3.04/3.25  # Proof object simplifying inferences  : 27
% 3.04/3.25  # Training examples: 0 positive, 0 negative
% 3.04/3.25  # Parsed axioms                        : 14
% 3.04/3.25  # Removed by relevancy pruning/SinE    : 0
% 3.04/3.25  # Initial clauses                      : 24
% 3.04/3.25  # Removed in clause preprocessing      : 2
% 3.04/3.25  # Initial clauses in saturation        : 22
% 3.04/3.25  # Processed clauses                    : 7007
% 3.04/3.25  # ...of these trivial                  : 42
% 3.04/3.25  # ...subsumed                          : 5918
% 3.04/3.25  # ...remaining for further processing  : 1047
% 3.04/3.25  # Other redundant clauses eliminated   : 2
% 3.04/3.25  # Clauses deleted for lack of memory   : 0
% 3.04/3.25  # Backward-subsumed                    : 23
% 3.04/3.25  # Backward-rewritten                   : 65
% 3.04/3.25  # Generated clauses                    : 322282
% 3.04/3.25  # ...of the previous two non-trivial   : 314784
% 3.04/3.25  # Contextual simplify-reflections      : 38
% 3.04/3.25  # Paramodulations                      : 322200
% 3.04/3.25  # Factorizations                       : 4
% 3.04/3.25  # Equation resolutions                 : 78
% 3.04/3.25  # Propositional unsat checks           : 0
% 3.04/3.25  #    Propositional check models        : 0
% 3.04/3.25  #    Propositional check unsatisfiable : 0
% 3.04/3.25  #    Propositional clauses             : 0
% 3.04/3.25  #    Propositional clauses after purity: 0
% 3.04/3.25  #    Propositional unsat core size     : 0
% 3.04/3.25  #    Propositional preprocessing time  : 0.000
% 3.04/3.25  #    Propositional encoding time       : 0.000
% 3.04/3.25  #    Propositional solver time         : 0.000
% 3.04/3.25  #    Success case prop preproc time    : 0.000
% 3.04/3.25  #    Success case prop encoding time   : 0.000
% 3.04/3.25  #    Success case prop solver time     : 0.000
% 3.04/3.25  # Current number of processed clauses  : 957
% 3.04/3.25  #    Positive orientable unit clauses  : 29
% 3.04/3.25  #    Positive unorientable unit clauses: 4
% 3.04/3.25  #    Negative unit clauses             : 3
% 3.04/3.25  #    Non-unit-clauses                  : 921
% 3.04/3.25  # Current number of unprocessed clauses: 307570
% 3.04/3.25  # ...number of literals in the above   : 1391807
% 3.04/3.25  # Current number of archived formulas  : 0
% 3.04/3.25  # Current number of archived clauses   : 90
% 3.04/3.25  # Clause-clause subsumption calls (NU) : 206696
% 3.04/3.25  # Rec. Clause-clause subsumption calls : 144323
% 3.04/3.25  # Non-unit clause-clause subsumptions  : 5588
% 3.04/3.25  # Unit Clause-clause subsumption calls : 274
% 3.04/3.25  # Rewrite failures with RHS unbound    : 0
% 3.04/3.25  # BW rewrite match attempts            : 252
% 3.04/3.25  # BW rewrite match successes           : 159
% 3.04/3.25  # Condensation attempts                : 0
% 3.04/3.25  # Condensation successes               : 0
% 3.04/3.25  # Termbank termtop insertions          : 8791195
% 3.10/3.26  
% 3.10/3.26  # -------------------------------------------------
% 3.10/3.26  # User time                : 2.772 s
% 3.10/3.26  # System time              : 0.145 s
% 3.10/3.26  # Total time               : 2.917 s
% 3.10/3.26  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
