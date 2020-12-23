%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:18 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 257 expanded)
%              Number of clauses        :   58 ( 117 expanded)
%              Number of leaves         :   17 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  177 ( 563 expanded)
%              Number of equality atoms :   54 ( 142 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t41_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

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

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(c_0_17,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X30,X29)
        | r1_tarski(X30,X28)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r1_tarski(X31,X28)
        | r2_hidden(X31,X29)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r2_hidden(esk1_2(X32,X33),X33)
        | ~ r1_tarski(esk1_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) )
      & ( r2_hidden(esk1_2(X32,X33),X33)
        | r1_tarski(esk1_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t41_subset_1])).

fof(c_0_19,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_20,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X36,X35)
        | r2_hidden(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ r2_hidden(X36,X35)
        | m1_subset_1(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ m1_subset_1(X36,X35)
        | v1_xboole_0(X36)
        | ~ v1_xboole_0(X35) )
      & ( ~ v1_xboole_0(X36)
        | m1_subset_1(X36,X35)
        | ~ v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_24,plain,(
    ! [X39] : ~ v1_xboole_0(k1_zfmisc_1(X39)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_25,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_26,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_27,plain,(
    ! [X15] : r1_tarski(k1_xboole_0,X15) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_28,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(k4_xboole_0(X23,X24),X25)
      | r1_tarski(X23,k2_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X18,X19] : k2_xboole_0(X18,k4_xboole_0(X19,X18)) = k2_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_37,plain,(
    ! [X16,X17] : r1_tarski(k4_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_39])).

fof(c_0_50,plain,(
    ! [X20,X21,X22] : k4_xboole_0(k4_xboole_0(X20,X21),X22) = k4_xboole_0(X20,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_40])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_40])).

fof(c_0_53,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X13,X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_51]),c_0_51])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_58]),c_0_59]),c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_58])).

fof(c_0_66,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | k3_subset_1(X37,X38) = k4_xboole_0(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_67,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | k4_subset_1(X40,X41,X42) = k2_xboole_0(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,esk4_0),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_70,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_72,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk4_0),k2_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_69]),c_0_35])).

cnf(c_0_76,plain,
    ( k3_subset_1(X1,X2) = k4_xboole_0(X1,X2)
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_35])).

cnf(c_0_77,plain,
    ( k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X3,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_71]),c_0_35])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk4_0),k2_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_47])).

cnf(c_0_80,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_75]),c_0_47])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_82,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,X1) = k2_xboole_0(esk3_0,X1)
    | ~ r2_hidden(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_69])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k2_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_54])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,esk4_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_46])).

cnf(c_0_88,plain,
    ( k3_subset_1(k2_xboole_0(X1,X2),X2) = k4_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_85]),c_0_47])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)) = k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_57])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.39/0.60  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.39/0.60  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.39/0.60  #
% 0.39/0.60  # Preprocessing time       : 0.027 s
% 0.39/0.60  # Presaturation interreduction done
% 0.39/0.60  
% 0.39/0.60  # Proof found!
% 0.39/0.60  # SZS status Theorem
% 0.39/0.60  # SZS output start CNFRefutation
% 0.39/0.60  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.39/0.60  fof(t41_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 0.39/0.60  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.39/0.60  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.39/0.60  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.39/0.60  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.39/0.60  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.39/0.60  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.39/0.60  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.39/0.60  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.39/0.60  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.39/0.60  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.39/0.60  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.39/0.60  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.39/0.60  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.39/0.60  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.39/0.60  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.39/0.60  fof(c_0_17, plain, ![X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X30,X29)|r1_tarski(X30,X28)|X29!=k1_zfmisc_1(X28))&(~r1_tarski(X31,X28)|r2_hidden(X31,X29)|X29!=k1_zfmisc_1(X28)))&((~r2_hidden(esk1_2(X32,X33),X33)|~r1_tarski(esk1_2(X32,X33),X32)|X33=k1_zfmisc_1(X32))&(r2_hidden(esk1_2(X32,X33),X33)|r1_tarski(esk1_2(X32,X33),X32)|X33=k1_zfmisc_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.39/0.60  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t41_subset_1])).
% 0.39/0.60  fof(c_0_19, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.39/0.60  fof(c_0_20, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.39/0.60  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.60  fof(c_0_22, plain, ![X35, X36]:(((~m1_subset_1(X36,X35)|r2_hidden(X36,X35)|v1_xboole_0(X35))&(~r2_hidden(X36,X35)|m1_subset_1(X36,X35)|v1_xboole_0(X35)))&((~m1_subset_1(X36,X35)|v1_xboole_0(X36)|~v1_xboole_0(X35))&(~v1_xboole_0(X36)|m1_subset_1(X36,X35)|~v1_xboole_0(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.39/0.60  fof(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.39/0.60  fof(c_0_24, plain, ![X39]:~v1_xboole_0(k1_zfmisc_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.39/0.60  fof(c_0_25, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.39/0.60  fof(c_0_26, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.39/0.60  fof(c_0_27, plain, ![X15]:r1_tarski(k1_xboole_0,X15), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.39/0.60  fof(c_0_28, plain, ![X23, X24, X25]:(~r1_tarski(k4_xboole_0(X23,X24),X25)|r1_tarski(X23,k2_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.39/0.60  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.60  fof(c_0_30, plain, ![X18, X19]:k2_xboole_0(X18,k4_xboole_0(X19,X18))=k2_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.39/0.60  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.39/0.60  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_21])).
% 0.39/0.60  cnf(c_0_33, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.60  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.60  cnf(c_0_35, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.39/0.60  fof(c_0_36, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.39/0.60  fof(c_0_37, plain, ![X16, X17]:r1_tarski(k4_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.39/0.60  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.60  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.60  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.60  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.60  cnf(c_0_42, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.39/0.60  cnf(c_0_43, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_29])).
% 0.39/0.60  cnf(c_0_44, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.39/0.60  cnf(c_0_45, plain, (k2_xboole_0(X1,X2)=X2|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.39/0.60  cnf(c_0_46, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.39/0.60  cnf(c_0_47, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.39/0.60  cnf(c_0_48, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.39/0.60  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_39])).
% 0.39/0.60  fof(c_0_50, plain, ![X20, X21, X22]:k4_xboole_0(k4_xboole_0(X20,X21),X22)=k4_xboole_0(X20,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.39/0.60  cnf(c_0_51, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_31, c_0_40])).
% 0.39/0.60  cnf(c_0_52, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_40])).
% 0.39/0.60  fof(c_0_53, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X13,X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.39/0.60  cnf(c_0_54, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.39/0.60  cnf(c_0_55, negated_conjecture, (k2_xboole_0(esk2_0,esk4_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.39/0.60  cnf(c_0_56, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.39/0.60  cnf(c_0_57, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.39/0.60  cnf(c_0_58, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_51]), c_0_51])).
% 0.39/0.60  cnf(c_0_59, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_48])).
% 0.39/0.60  cnf(c_0_60, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.39/0.60  cnf(c_0_61, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.39/0.60  cnf(c_0_62, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3))),X3)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.39/0.60  cnf(c_0_63, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_58]), c_0_59]), c_0_59])).
% 0.39/0.60  cnf(c_0_64, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.39/0.60  cnf(c_0_65, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_58])).
% 0.39/0.60  fof(c_0_66, plain, ![X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|k3_subset_1(X37,X38)=k4_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.39/0.60  fof(c_0_67, plain, ![X40, X41, X42]:(~m1_subset_1(X41,k1_zfmisc_1(X40))|~m1_subset_1(X42,k1_zfmisc_1(X40))|k4_subset_1(X40,X41,X42)=k2_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.39/0.60  cnf(c_0_68, negated_conjecture, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,esk4_0),X1),esk2_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.39/0.60  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.60  cnf(c_0_70, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.39/0.60  cnf(c_0_71, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.60  cnf(c_0_72, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.39/0.60  cnf(c_0_73, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.60  cnf(c_0_74, negated_conjecture, (r1_tarski(k2_xboole_0(X1,esk4_0),k2_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_42, c_0_68])).
% 0.39/0.60  cnf(c_0_75, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_69]), c_0_35])).
% 0.39/0.60  cnf(c_0_76, plain, (k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_35])).
% 0.39/0.60  cnf(c_0_77, plain, (k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r2_hidden(X3,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_71]), c_0_35])).
% 0.39/0.60  cnf(c_0_78, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_73])).
% 0.39/0.60  cnf(c_0_79, negated_conjecture, (r1_tarski(k2_xboole_0(X1,esk4_0),k2_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_74, c_0_47])).
% 0.39/0.60  cnf(c_0_80, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_75]), c_0_47])).
% 0.39/0.60  cnf(c_0_81, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.60  cnf(c_0_82, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k4_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_76, c_0_75])).
% 0.39/0.60  cnf(c_0_83, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,X1)=k2_xboole_0(esk3_0,X1)|~r2_hidden(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_77, c_0_69])).
% 0.39/0.60  cnf(c_0_84, plain, (r2_hidden(X1,k1_zfmisc_1(k2_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_78, c_0_54])).
% 0.39/0.60  cnf(c_0_85, negated_conjecture, (r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.39/0.60  cnf(c_0_86, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.39/0.60  cnf(c_0_87, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,esk4_0)=k2_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_83, c_0_46])).
% 0.39/0.60  cnf(c_0_88, plain, (k3_subset_1(k2_xboole_0(X1,X2),X2)=k4_xboole_0(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_76, c_0_84])).
% 0.39/0.60  cnf(c_0_89, negated_conjecture, (k2_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_85]), c_0_47])).
% 0.39/0.60  cnf(c_0_90, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_86, c_0_87])).
% 0.39/0.60  cnf(c_0_91, negated_conjecture, (k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0))=k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_57])).
% 0.39/0.60  cnf(c_0_92, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91]), c_0_48])]), ['proof']).
% 0.39/0.60  # SZS output end CNFRefutation
% 0.39/0.60  # Proof object total steps             : 93
% 0.39/0.60  # Proof object clause steps            : 58
% 0.39/0.60  # Proof object formula steps           : 35
% 0.39/0.60  # Proof object conjectures             : 24
% 0.39/0.60  # Proof object clause conjectures      : 21
% 0.39/0.60  # Proof object formula conjectures     : 3
% 0.39/0.60  # Proof object initial clauses used    : 22
% 0.39/0.60  # Proof object initial formulas used   : 17
% 0.39/0.60  # Proof object generating inferences   : 29
% 0.39/0.60  # Proof object simplifying inferences  : 23
% 0.39/0.60  # Training examples: 0 positive, 0 negative
% 0.39/0.60  # Parsed axioms                        : 17
% 0.39/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.60  # Initial clauses                      : 27
% 0.39/0.60  # Removed in clause preprocessing      : 1
% 0.39/0.60  # Initial clauses in saturation        : 26
% 0.39/0.60  # Processed clauses                    : 3010
% 0.39/0.60  # ...of these trivial                  : 331
% 0.39/0.60  # ...subsumed                          : 1914
% 0.39/0.60  # ...remaining for further processing  : 765
% 0.39/0.60  # Other redundant clauses eliminated   : 4
% 0.39/0.60  # Clauses deleted for lack of memory   : 0
% 0.39/0.60  # Backward-subsumed                    : 5
% 0.39/0.60  # Backward-rewritten                   : 29
% 0.39/0.60  # Generated clauses                    : 24679
% 0.39/0.60  # ...of the previous two non-trivial   : 17207
% 0.39/0.60  # Contextual simplify-reflections      : 5
% 0.39/0.60  # Paramodulations                      : 24669
% 0.39/0.60  # Factorizations                       : 6
% 0.39/0.60  # Equation resolutions                 : 4
% 0.39/0.60  # Propositional unsat checks           : 0
% 0.39/0.60  #    Propositional check models        : 0
% 0.39/0.60  #    Propositional check unsatisfiable : 0
% 0.39/0.60  #    Propositional clauses             : 0
% 0.39/0.60  #    Propositional clauses after purity: 0
% 0.39/0.60  #    Propositional unsat core size     : 0
% 0.39/0.60  #    Propositional preprocessing time  : 0.000
% 0.39/0.60  #    Propositional encoding time       : 0.000
% 0.39/0.60  #    Propositional solver time         : 0.000
% 0.39/0.60  #    Success case prop preproc time    : 0.000
% 0.39/0.60  #    Success case prop encoding time   : 0.000
% 0.39/0.60  #    Success case prop solver time     : 0.000
% 0.39/0.60  # Current number of processed clauses  : 702
% 0.39/0.60  #    Positive orientable unit clauses  : 240
% 0.39/0.60  #    Positive unorientable unit clauses: 12
% 0.39/0.60  #    Negative unit clauses             : 1
% 0.39/0.60  #    Non-unit-clauses                  : 449
% 0.39/0.60  # Current number of unprocessed clauses: 14177
% 0.39/0.60  # ...number of literals in the above   : 31099
% 0.39/0.60  # Current number of archived formulas  : 0
% 0.39/0.60  # Current number of archived clauses   : 60
% 0.39/0.60  # Clause-clause subsumption calls (NU) : 49456
% 0.39/0.60  # Rec. Clause-clause subsumption calls : 40492
% 0.39/0.60  # Non-unit clause-clause subsumptions  : 1811
% 0.39/0.60  # Unit Clause-clause subsumption calls : 2840
% 0.39/0.60  # Rewrite failures with RHS unbound    : 27
% 0.39/0.60  # BW rewrite match attempts            : 830
% 0.39/0.60  # BW rewrite match successes           : 52
% 0.39/0.60  # Condensation attempts                : 0
% 0.39/0.60  # Condensation successes               : 0
% 0.39/0.60  # Termbank termtop insertions          : 245023
% 0.39/0.60  
% 0.39/0.60  # -------------------------------------------------
% 0.39/0.60  # User time                : 0.242 s
% 0.39/0.60  # System time              : 0.012 s
% 0.39/0.60  # Total time               : 0.255 s
% 0.39/0.60  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
