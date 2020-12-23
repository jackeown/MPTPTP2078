%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:40 EST 2020

% Result     : Theorem 5.59s
% Output     : CNFRefutation 5.59s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 792 expanded)
%              Number of clauses        :   80 ( 375 expanded)
%              Number of leaves         :   20 ( 197 expanded)
%              Depth                    :   17
%              Number of atoms          :  258 (1978 expanded)
%              Number of equality atoms :   30 ( 312 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_21,plain,(
    ! [X53,X54] :
      ( ( ~ m1_subset_1(X54,X53)
        | r2_hidden(X54,X53)
        | v1_xboole_0(X53) )
      & ( ~ r2_hidden(X54,X53)
        | m1_subset_1(X54,X53)
        | v1_xboole_0(X53) )
      & ( ~ m1_subset_1(X54,X53)
        | v1_xboole_0(X54)
        | ~ v1_xboole_0(X53) )
      & ( ~ v1_xboole_0(X54)
        | m1_subset_1(X54,X53)
        | ~ v1_xboole_0(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) )
    & ( r1_tarski(esk3_0,esk4_0)
      | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_23,plain,(
    ! [X57] : ~ v1_xboole_0(k1_zfmisc_1(X57)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_24,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_25,plain,(
    ! [X51,X52] :
      ( ~ r1_tarski(X51,X52)
      | r1_tarski(k1_zfmisc_1(X51),k1_zfmisc_1(X52)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_26,plain,(
    ! [X47,X48] :
      ( ( ~ r1_tarski(k1_tarski(X47),X48)
        | r2_hidden(X47,X48) )
      & ( ~ r2_hidden(X47,X48)
        | r1_tarski(k1_tarski(X47),X48) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_35,plain,(
    ! [X40,X41,X42,X43,X44,X45] :
      ( ( ~ r2_hidden(X42,X41)
        | r1_tarski(X42,X40)
        | X41 != k1_zfmisc_1(X40) )
      & ( ~ r1_tarski(X43,X40)
        | r2_hidden(X43,X41)
        | X41 != k1_zfmisc_1(X40) )
      & ( ~ r2_hidden(esk1_2(X44,X45),X45)
        | ~ r1_tarski(esk1_2(X44,X45),X44)
        | X45 = k1_zfmisc_1(X44) )
      & ( r2_hidden(esk1_2(X44,X45),X45)
        | r1_tarski(esk1_2(X44,X45),X44)
        | X45 = k1_zfmisc_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k1_tarski(esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_34]),c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k1_tarski(esk4_0),k1_zfmisc_1(X1))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_42,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(k4_xboole_0(X24,X25),X26)
      | r1_tarski(X24,k2_xboole_0(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_43,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_44,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_38])).

fof(c_0_46,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(X27,k2_xboole_0(X28,X29))
      | ~ r1_xboole_0(X27,X29)
      | r1_tarski(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),k1_zfmisc_1(X1))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_45])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_51])).

fof(c_0_57,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_58,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_59,plain,(
    ! [X30,X31] : r1_xboole_0(k4_xboole_0(X30,X31),X31) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_33])).

fof(c_0_61,plain,(
    ! [X15,X16] : r1_tarski(k3_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_52])).

fof(c_0_63,plain,(
    ! [X55,X56] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(X55))
      | k3_subset_1(X55,X56) = k4_xboole_0(X55,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk2_0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_68,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_69,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_60])).

cnf(c_0_71,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_38])).

cnf(c_0_74,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_xboole_0(esk4_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_76,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_50])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(esk2_0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_73])).

cnf(c_0_82,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_50])).

fof(c_0_83,plain,(
    ! [X34,X35,X36] :
      ( ~ r1_tarski(X34,X35)
      | r1_xboole_0(X34,k4_xboole_0(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_84,plain,(
    ! [X37,X38,X39] :
      ( ~ r1_tarski(X37,X38)
      | ~ r1_xboole_0(X37,X39)
      | r1_tarski(X37,k4_xboole_0(X38,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

fof(c_0_85,plain,(
    ! [X22,X23] : r1_tarski(k4_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_xboole_0(esk4_0,k5_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_87,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_67])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_65])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_71])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_93,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_95,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_96,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk4_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])])).

cnf(c_0_98,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_67])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_76])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_67])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0)))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_28])])).

cnf(c_0_102,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_93,c_0_50])).

cnf(c_0_103,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_94,c_0_50])).

cnf(c_0_104,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_95,c_0_50])).

cnf(c_0_105,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_87]),c_0_100])])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | ~ r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_101])).

cnf(c_0_108,plain,
    ( r1_xboole_0(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_102,c_0_82])).

cnf(c_0_109,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X3)))
    | ~ r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk4_0) = k3_subset_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_105]),c_0_28])])).

cnf(c_0_111,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_106]),c_0_98])])).

cnf(c_0_112,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_34]),c_0_56])])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)))
    | ~ r1_xboole_0(k3_subset_1(esk2_0,esk4_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_105]),c_0_110]),c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk3_0) = k3_subset_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_111]),c_0_34])])).

cnf(c_0_116,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113])])).

cnf(c_0_117,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_102])).

cnf(c_0_118,negated_conjecture,
    ( ~ r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_111]),c_0_115]),c_0_116])).

cnf(c_0_119,plain,
    ( r1_xboole_0(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_117,c_0_82])).

cnf(c_0_120,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_28]),c_0_113])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:36:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 5.59/5.77  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 5.59/5.77  # and selection function SelectComplexExceptUniqMaxHorn.
% 5.59/5.77  #
% 5.59/5.77  # Preprocessing time       : 0.044 s
% 5.59/5.77  # Presaturation interreduction done
% 5.59/5.77  
% 5.59/5.77  # Proof found!
% 5.59/5.77  # SZS status Theorem
% 5.59/5.77  # SZS output start CNFRefutation
% 5.59/5.77  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 5.59/5.77  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.59/5.77  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.59/5.77  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.59/5.77  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 5.59/5.77  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.59/5.77  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.59/5.77  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.59/5.77  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.59/5.77  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.59/5.77  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 5.59/5.77  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.59/5.77  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.59/5.77  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.59/5.77  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.59/5.77  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.59/5.77  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.59/5.77  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.59/5.77  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 5.59/5.77  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.59/5.77  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 5.59/5.77  fof(c_0_21, plain, ![X53, X54]:(((~m1_subset_1(X54,X53)|r2_hidden(X54,X53)|v1_xboole_0(X53))&(~r2_hidden(X54,X53)|m1_subset_1(X54,X53)|v1_xboole_0(X53)))&((~m1_subset_1(X54,X53)|v1_xboole_0(X54)|~v1_xboole_0(X53))&(~v1_xboole_0(X54)|m1_subset_1(X54,X53)|~v1_xboole_0(X53)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 5.59/5.77  fof(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))&(r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 5.59/5.77  fof(c_0_23, plain, ![X57]:~v1_xboole_0(k1_zfmisc_1(X57)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 5.59/5.77  fof(c_0_24, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_tarski(X18,X19)|r1_tarski(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 5.59/5.77  fof(c_0_25, plain, ![X51, X52]:(~r1_tarski(X51,X52)|r1_tarski(k1_zfmisc_1(X51),k1_zfmisc_1(X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 5.59/5.77  fof(c_0_26, plain, ![X47, X48]:((~r1_tarski(k1_tarski(X47),X48)|r2_hidden(X47,X48))&(~r2_hidden(X47,X48)|r1_tarski(k1_tarski(X47),X48))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 5.59/5.77  cnf(c_0_27, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.59/5.77  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.59/5.77  cnf(c_0_29, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.59/5.77  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.59/5.77  cnf(c_0_31, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.59/5.77  cnf(c_0_32, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 5.59/5.77  cnf(c_0_33, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 5.59/5.77  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.59/5.77  fof(c_0_35, plain, ![X40, X41, X42, X43, X44, X45]:(((~r2_hidden(X42,X41)|r1_tarski(X42,X40)|X41!=k1_zfmisc_1(X40))&(~r1_tarski(X43,X40)|r2_hidden(X43,X41)|X41!=k1_zfmisc_1(X40)))&((~r2_hidden(esk1_2(X44,X45),X45)|~r1_tarski(esk1_2(X44,X45),X44)|X45=k1_zfmisc_1(X44))&(r2_hidden(esk1_2(X44,X45),X45)|r1_tarski(esk1_2(X44,X45),X44)|X45=k1_zfmisc_1(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 5.59/5.77  cnf(c_0_36, plain, (r1_tarski(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k1_zfmisc_1(X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 5.59/5.77  cnf(c_0_37, negated_conjecture, (r1_tarski(k1_tarski(esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 5.59/5.77  cnf(c_0_38, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_34]), c_0_29])).
% 5.59/5.77  cnf(c_0_39, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 5.59/5.77  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 5.59/5.77  cnf(c_0_41, negated_conjecture, (r1_tarski(k1_tarski(esk4_0),k1_zfmisc_1(X1))|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 5.59/5.77  fof(c_0_42, plain, ![X24, X25, X26]:(~r1_tarski(k4_xboole_0(X24,X25),X26)|r1_tarski(X24,k2_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 5.59/5.77  fof(c_0_43, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 5.59/5.77  fof(c_0_44, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 5.59/5.77  cnf(c_0_45, negated_conjecture, (r1_tarski(k1_tarski(esk3_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_38])).
% 5.59/5.77  fof(c_0_46, plain, ![X27, X28, X29]:(~r1_tarski(X27,k2_xboole_0(X28,X29))|~r1_xboole_0(X27,X29)|r1_tarski(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 5.59/5.77  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_39])).
% 5.59/5.77  cnf(c_0_48, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(X1))|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 5.59/5.77  cnf(c_0_49, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 5.59/5.77  cnf(c_0_50, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.59/5.77  cnf(c_0_51, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 5.59/5.77  cnf(c_0_52, negated_conjecture, (r1_tarski(k1_tarski(esk3_0),k1_zfmisc_1(X1))|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_45])).
% 5.59/5.77  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 5.59/5.77  cnf(c_0_54, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 5.59/5.77  cnf(c_0_55, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 5.59/5.77  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_51])).
% 5.59/5.77  fof(c_0_57, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 5.59/5.77  fof(c_0_58, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 5.59/5.77  fof(c_0_59, plain, ![X30, X31]:r1_xboole_0(k4_xboole_0(X30,X31),X31), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 5.59/5.77  cnf(c_0_60, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_47, c_0_33])).
% 5.59/5.77  fof(c_0_61, plain, ![X15, X16]:r1_tarski(k3_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 5.59/5.77  cnf(c_0_62, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(X1))|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_52])).
% 5.59/5.77  fof(c_0_63, plain, ![X55, X56]:(~m1_subset_1(X56,k1_zfmisc_1(X55))|k3_subset_1(X55,X56)=k4_xboole_0(X55,X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 5.59/5.77  cnf(c_0_64, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(esk2_0,k2_xboole_0(X1,X2))|~r1_xboole_0(esk4_0,X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 5.59/5.77  cnf(c_0_65, plain, (r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 5.59/5.77  cnf(c_0_66, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 5.59/5.77  cnf(c_0_67, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.59/5.77  fof(c_0_68, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 5.59/5.77  cnf(c_0_69, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 5.59/5.77  cnf(c_0_70, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_60])).
% 5.59/5.77  cnf(c_0_71, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 5.59/5.77  cnf(c_0_72, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_62])).
% 5.59/5.77  cnf(c_0_73, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_47, c_0_38])).
% 5.59/5.77  cnf(c_0_74, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 5.59/5.77  cnf(c_0_75, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_xboole_0(esk4_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 5.59/5.77  cnf(c_0_76, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 5.59/5.77  cnf(c_0_77, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 5.59/5.77  cnf(c_0_78, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_69, c_0_50])).
% 5.59/5.77  cnf(c_0_79, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 5.59/5.77  cnf(c_0_80, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(esk2_0,k2_xboole_0(X1,X2))|~r1_xboole_0(esk3_0,X2)), inference(spm,[status(thm)],[c_0_53, c_0_72])).
% 5.59/5.77  cnf(c_0_81, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_73])).
% 5.59/5.77  cnf(c_0_82, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_74, c_0_50])).
% 5.59/5.77  fof(c_0_83, plain, ![X34, X35, X36]:(~r1_tarski(X34,X35)|r1_xboole_0(X34,k4_xboole_0(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 5.59/5.77  fof(c_0_84, plain, ![X37, X38, X39]:(~r1_tarski(X37,X38)|~r1_xboole_0(X37,X39)|r1_tarski(X37,k4_xboole_0(X38,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 5.59/5.77  fof(c_0_85, plain, ![X22, X23]:r1_tarski(k4_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 5.59/5.77  cnf(c_0_86, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(X1,esk2_0)|~r1_xboole_0(esk4_0,k5_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 5.59/5.77  cnf(c_0_87, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 5.59/5.77  cnf(c_0_88, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_79, c_0_67])).
% 5.59/5.77  cnf(c_0_89, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_80, c_0_65])).
% 5.59/5.77  cnf(c_0_90, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_81, c_0_71])).
% 5.59/5.77  cnf(c_0_91, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k3_subset_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_55, c_0_82])).
% 5.59/5.77  cnf(c_0_92, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.59/5.77  cnf(c_0_93, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 5.59/5.77  cnf(c_0_94, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 5.59/5.77  cnf(c_0_95, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 5.59/5.77  cnf(c_0_96, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 5.59/5.77  cnf(c_0_97, negated_conjecture, (r1_tarski(esk4_0,k3_xboole_0(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])])).
% 5.59/5.77  cnf(c_0_98, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_71, c_0_67])).
% 5.59/5.77  cnf(c_0_99, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(X1,esk2_0)|~r1_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_89, c_0_76])).
% 5.59/5.77  cnf(c_0_100, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_90, c_0_67])).
% 5.59/5.77  cnf(c_0_101, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0)))|r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_28])])).
% 5.59/5.77  cnf(c_0_102, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_93, c_0_50])).
% 5.59/5.77  cnf(c_0_103, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_94, c_0_50])).
% 5.59/5.77  cnf(c_0_104, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_95, c_0_50])).
% 5.59/5.77  cnf(c_0_105, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])])).
% 5.59/5.77  cnf(c_0_106, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_87]), c_0_100])])).
% 5.59/5.77  cnf(c_0_107, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_80, c_0_101])).
% 5.59/5.77  cnf(c_0_108, plain, (r1_xboole_0(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_102, c_0_82])).
% 5.59/5.77  cnf(c_0_109, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X3)))|~r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 5.59/5.77  cnf(c_0_110, negated_conjecture, (k5_xboole_0(esk2_0,esk4_0)=k3_subset_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_105]), c_0_28])])).
% 5.59/5.77  cnf(c_0_111, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_106]), c_0_98])])).
% 5.59/5.77  cnf(c_0_112, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.59/5.77  cnf(c_0_113, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_34]), c_0_56])])).
% 5.59/5.77  cnf(c_0_114, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)))|~r1_xboole_0(k3_subset_1(esk2_0,esk4_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_105]), c_0_110]), c_0_110])).
% 5.59/5.77  cnf(c_0_115, negated_conjecture, (k5_xboole_0(esk2_0,esk3_0)=k3_subset_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_111]), c_0_34])])).
% 5.59/5.77  cnf(c_0_116, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113])])).
% 5.59/5.77  cnf(c_0_117, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_77, c_0_102])).
% 5.59/5.77  cnf(c_0_118, negated_conjecture, (~r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_111]), c_0_115]), c_0_116])).
% 5.59/5.77  cnf(c_0_119, plain, (r1_xboole_0(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_117, c_0_82])).
% 5.59/5.77  cnf(c_0_120, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_28]), c_0_113])]), ['proof']).
% 5.59/5.77  # SZS output end CNFRefutation
% 5.59/5.77  # Proof object total steps             : 121
% 5.59/5.77  # Proof object clause steps            : 80
% 5.59/5.77  # Proof object formula steps           : 41
% 5.59/5.77  # Proof object conjectures             : 44
% 5.59/5.77  # Proof object clause conjectures      : 41
% 5.59/5.77  # Proof object formula conjectures     : 3
% 5.59/5.77  # Proof object initial clauses used    : 25
% 5.59/5.77  # Proof object initial formulas used   : 20
% 5.59/5.77  # Proof object generating inferences   : 46
% 5.59/5.77  # Proof object simplifying inferences  : 36
% 5.59/5.77  # Training examples: 0 positive, 0 negative
% 5.59/5.77  # Parsed axioms                        : 23
% 5.59/5.77  # Removed by relevancy pruning/SinE    : 0
% 5.59/5.77  # Initial clauses                      : 35
% 5.59/5.77  # Removed in clause preprocessing      : 1
% 5.59/5.77  # Initial clauses in saturation        : 34
% 5.59/5.77  # Processed clauses                    : 50520
% 5.59/5.77  # ...of these trivial                  : 593
% 5.59/5.77  # ...subsumed                          : 42946
% 5.59/5.77  # ...remaining for further processing  : 6981
% 5.59/5.77  # Other redundant clauses eliminated   : 4
% 5.59/5.77  # Clauses deleted for lack of memory   : 0
% 5.59/5.77  # Backward-subsumed                    : 1390
% 5.59/5.77  # Backward-rewritten                   : 515
% 5.59/5.77  # Generated clauses                    : 575943
% 5.59/5.77  # ...of the previous two non-trivial   : 522991
% 5.59/5.77  # Contextual simplify-reflections      : 172
% 5.59/5.77  # Paramodulations                      : 575937
% 5.59/5.77  # Factorizations                       : 2
% 5.59/5.77  # Equation resolutions                 : 4
% 5.59/5.77  # Propositional unsat checks           : 1
% 5.59/5.77  #    Propositional check models        : 0
% 5.59/5.77  #    Propositional check unsatisfiable : 0
% 5.59/5.77  #    Propositional clauses             : 0
% 5.59/5.77  #    Propositional clauses after purity: 0
% 5.59/5.77  #    Propositional unsat core size     : 0
% 5.59/5.77  #    Propositional preprocessing time  : 0.000
% 5.59/5.77  #    Propositional encoding time       : 0.158
% 5.59/5.77  #    Propositional solver time         : 0.050
% 5.59/5.77  #    Success case prop preproc time    : 0.000
% 5.59/5.77  #    Success case prop encoding time   : 0.000
% 5.59/5.77  #    Success case prop solver time     : 0.000
% 5.59/5.77  # Current number of processed clauses  : 5039
% 5.59/5.77  #    Positive orientable unit clauses  : 482
% 5.59/5.77  #    Positive unorientable unit clauses: 2
% 5.59/5.77  #    Negative unit clauses             : 152
% 5.59/5.77  #    Non-unit-clauses                  : 4403
% 5.59/5.77  # Current number of unprocessed clauses: 459981
% 5.59/5.77  # ...number of literals in the above   : 2367968
% 5.59/5.77  # Current number of archived formulas  : 0
% 5.59/5.77  # Current number of archived clauses   : 1939
% 5.59/5.77  # Clause-clause subsumption calls (NU) : 7612454
% 5.59/5.77  # Rec. Clause-clause subsumption calls : 4210809
% 5.59/5.77  # Non-unit clause-clause subsumptions  : 26252
% 5.59/5.77  # Unit Clause-clause subsumption calls : 222884
% 5.59/5.77  # Rewrite failures with RHS unbound    : 73
% 5.59/5.77  # BW rewrite match attempts            : 3666
% 5.59/5.77  # BW rewrite match successes           : 238
% 5.59/5.77  # Condensation attempts                : 0
% 5.59/5.77  # Condensation successes               : 0
% 5.59/5.77  # Termbank termtop insertions          : 10942856
% 5.59/5.79  
% 5.59/5.79  # -------------------------------------------------
% 5.59/5.79  # User time                : 5.266 s
% 5.59/5.79  # System time              : 0.182 s
% 5.59/5.79  # Total time               : 5.448 s
% 5.59/5.79  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
