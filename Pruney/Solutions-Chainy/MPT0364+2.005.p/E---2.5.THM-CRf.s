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
% DateTime   : Thu Dec  3 10:46:31 EST 2020

% Result     : Theorem 1.01s
% Output     : CNFRefutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  152 (11114 expanded)
%              Number of clauses        :  113 (5102 expanded)
%              Number of leaves         :   19 (2923 expanded)
%              Depth                    :   33
%              Number of atoms          :  247 (19210 expanded)
%              Number of equality atoms :   87 (7971 expanded)
%              Maximal formula depth    :   13 (   2 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

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

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
            <=> r1_tarski(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_subset_1])).

fof(c_0_20,plain,(
    ! [X36,X37,X38,X39,X40,X41] :
      ( ( ~ r2_hidden(X38,X37)
        | r1_tarski(X38,X36)
        | X37 != k1_zfmisc_1(X36) )
      & ( ~ r1_tarski(X39,X36)
        | r2_hidden(X39,X37)
        | X37 != k1_zfmisc_1(X36) )
      & ( ~ r2_hidden(esk1_2(X40,X41),X41)
        | ~ r1_tarski(esk1_2(X40,X41),X40)
        | X41 = k1_zfmisc_1(X40) )
      & ( r2_hidden(esk1_2(X40,X41),X41)
        | r1_tarski(esk1_2(X40,X41),X40)
        | X41 = k1_zfmisc_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_21,plain,(
    ! [X43,X44] :
      ( ( ~ m1_subset_1(X44,X43)
        | r2_hidden(X44,X43)
        | v1_xboole_0(X43) )
      & ( ~ r2_hidden(X44,X43)
        | m1_subset_1(X44,X43)
        | v1_xboole_0(X43) )
      & ( ~ m1_subset_1(X44,X43)
        | v1_xboole_0(X44)
        | ~ v1_xboole_0(X43) )
      & ( ~ v1_xboole_0(X44)
        | m1_subset_1(X44,X43)
        | ~ v1_xboole_0(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))
      | ~ r1_tarski(esk3_0,esk4_0) )
    & ( r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))
      | r1_tarski(esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_23,plain,(
    ! [X47] : ~ v1_xboole_0(k1_zfmisc_1(X47)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_xboole_0(X24,X25)
      | r1_xboole_0(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

fof(c_0_31,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,X30)
      | r1_xboole_0(X29,k4_xboole_0(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_32,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_39,plain,(
    ! [X10] : k3_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_tarski(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_42,plain,(
    ! [X35] : k5_xboole_0(X35,X35) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_43,plain,(
    ! [X16,X17] : r1_tarski(k3_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(X1,X1))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk4_0,k1_xboole_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_41])).

fof(c_0_49,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_45])).

fof(c_0_53,plain,(
    ! [X13,X14,X15] : k5_xboole_0(k3_xboole_0(X13,X14),k3_xboole_0(X15,X14)) = k3_xboole_0(k5_xboole_0(X13,X15),X14) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_54,plain,(
    ! [X22] : k5_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_55,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_xboole_0(X26,k4_xboole_0(X27,X28))
      | r1_xboole_0(X27,k4_xboole_0(X26,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k3_xboole_0(esk4_0,k5_xboole_0(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X1),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_58])).

fof(c_0_63,plain,(
    ! [X32,X33,X34] : k5_xboole_0(k5_xboole_0(X32,X33),X34) = k5_xboole_0(X32,k5_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_59,c_0_45])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))
    | ~ r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_36]),c_0_36])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_57])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X2,X2),X3)) = X1 ),
    inference(spm,[status(thm)],[c_0_64,c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(X1,k5_xboole_0(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68])).

fof(c_0_70,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_71,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_41]),c_0_69])])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_75,plain,(
    ! [X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(X45))
      | k3_subset_1(X45,X46) = k4_xboole_0(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_77,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k3_xboole_0(X18,X19)) = k4_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_72])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_73])).

cnf(c_0_80,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_59,c_0_74])).

cnf(c_0_81,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)) = k1_xboole_0
    | r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_84,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_45]),c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))
    | ~ r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_88,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_36])).

cnf(c_0_89,negated_conjecture,
    ( k3_xboole_0(k3_subset_1(esk2_0,esk4_0),k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))) = k3_subset_1(esk2_0,esk4_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_82]),c_0_59]),c_0_74])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_83]),c_0_27])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_36]),c_0_36])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_67])).

cnf(c_0_93,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(esk4_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_85])).

cnf(c_0_94,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_86,c_0_74])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk4_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_26])]),c_0_73])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_74]),c_0_73])).

cnf(c_0_97,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_73]),c_0_79])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_79])).

cnf(c_0_99,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))) = esk3_0
    | r1_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_89]),c_0_67]),c_0_64]),c_0_67]),c_0_64]),c_0_73])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_73])).

cnf(c_0_101,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_80])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_90])).

cnf(c_0_103,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_91]),c_0_86])).

cnf(c_0_104,plain,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(esk4_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_105,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_106,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_86])).

cnf(c_0_107,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)) = k5_xboole_0(esk3_0,esk3_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_73])).

cnf(c_0_108,plain,
    ( k3_subset_1(X1,X2) = k3_xboole_0(X1,k5_xboole_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_88,c_0_100])).

cnf(c_0_109,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_101])).

cnf(c_0_110,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_102])).

cnf(c_0_111,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(esk4_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_93])).

cnf(c_0_112,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X1)) = k5_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_41])).

cnf(c_0_113,plain,
    ( k3_xboole_0(esk4_0,k5_xboole_0(X1,X1)) = k5_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_114,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0)))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_88]),c_0_26])]),c_0_73]),c_0_96])).

cnf(c_0_115,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_94])])).

cnf(c_0_116,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0))) = k5_xboole_0(esk3_0,esk3_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_26])]),c_0_74])).

cnf(c_0_117,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_109]),c_0_109]),c_0_59]),c_0_59])).

cnf(c_0_118,negated_conjecture,
    ( r1_xboole_0(X1,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_78])).

cnf(c_0_119,negated_conjecture,
    ( r1_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_72])).

cnf(c_0_120,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(esk2_0,esk2_0)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_112]),c_0_113])).

cnf(c_0_121,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk2_0) = k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_114,c_0_115]),c_0_93]),c_0_112]),c_0_113])).

cnf(c_0_122,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0))) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_116,c_0_115])).

cnf(c_0_123,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_124,negated_conjecture,
    ( r1_xboole_0(X1,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_119])).

cnf(c_0_125,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(esk3_0,esk3_0)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_121]),c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk2_0)),X1) ),
    inference(rw,[status(thm)],[c_0_123,c_0_100])).

cnf(c_0_127,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_117,c_0_124])).

cnf(c_0_128,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_73])).

cnf(c_0_129,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk2_0)),X1) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_130,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk2_0)),X1) ),
    inference(rw,[status(thm)],[c_0_127,c_0_100])).

cnf(c_0_131,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_128,c_0_99])).

cnf(c_0_132,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk2_0)) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_129]),c_0_64]),c_0_129])).

cnf(c_0_133,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk2_0)),X1) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_130])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0))))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_88]),c_0_73]),c_0_96]),c_0_26])])).

cnf(c_0_135,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_132]),c_0_64]),c_0_86])).

cnf(c_0_136,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk2_0)) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_133]),c_0_64]),c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0)))) ),
    inference(sr,[status(thm)],[c_0_134,c_0_115])).

cnf(c_0_138,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0)) = k5_xboole_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_132]),c_0_67]),c_0_64]),c_0_67]),c_0_74]),c_0_86]),c_0_73])).

cnf(c_0_139,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_72,c_0_100])).

cnf(c_0_140,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(X1,esk2_0)) = k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_135]),c_0_73])).

cnf(c_0_141,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_136]),c_0_86]),c_0_86])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_143,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_86])).

cnf(c_0_144,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,esk4_0)) = k5_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_74]),c_0_74])).

cnf(c_0_145,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_74])).

cnf(c_0_146,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_142])).

cnf(c_0_147,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk2_0)),k5_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_145])).

cnf(c_0_148,negated_conjecture,
    ( r1_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_149,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk4_0)) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_148])).

cnf(c_0_150,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_149]),c_0_86]),c_0_86])).

cnf(c_0_151,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_150]),c_0_115]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:25:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.01/1.19  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.01/1.19  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.01/1.19  #
% 1.01/1.19  # Preprocessing time       : 0.027 s
% 1.01/1.19  # Presaturation interreduction done
% 1.01/1.19  
% 1.01/1.19  # Proof found!
% 1.01/1.19  # SZS status Theorem
% 1.01/1.19  # SZS output start CNFRefutation
% 1.01/1.19  fof(t44_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,k3_subset_1(X1,X3))<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 1.01/1.19  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.01/1.19  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.01/1.19  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.01/1.19  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.01/1.19  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.01/1.19  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.01/1.19  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.01/1.19  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.01/1.19  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.01/1.19  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.01/1.19  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 1.01/1.19  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.01/1.19  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 1.01/1.19  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 1.01/1.19  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.01/1.19  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.01/1.19  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.01/1.19  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.01/1.19  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,k3_subset_1(X1,X3))<=>r1_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t44_subset_1])).
% 1.01/1.19  fof(c_0_20, plain, ![X36, X37, X38, X39, X40, X41]:(((~r2_hidden(X38,X37)|r1_tarski(X38,X36)|X37!=k1_zfmisc_1(X36))&(~r1_tarski(X39,X36)|r2_hidden(X39,X37)|X37!=k1_zfmisc_1(X36)))&((~r2_hidden(esk1_2(X40,X41),X41)|~r1_tarski(esk1_2(X40,X41),X40)|X41=k1_zfmisc_1(X40))&(r2_hidden(esk1_2(X40,X41),X41)|r1_tarski(esk1_2(X40,X41),X40)|X41=k1_zfmisc_1(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 1.01/1.19  fof(c_0_21, plain, ![X43, X44]:(((~m1_subset_1(X44,X43)|r2_hidden(X44,X43)|v1_xboole_0(X43))&(~r2_hidden(X44,X43)|m1_subset_1(X44,X43)|v1_xboole_0(X43)))&((~m1_subset_1(X44,X43)|v1_xboole_0(X44)|~v1_xboole_0(X43))&(~v1_xboole_0(X44)|m1_subset_1(X44,X43)|~v1_xboole_0(X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 1.01/1.19  fof(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))|~r1_tarski(esk3_0,esk4_0))&(r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))|r1_tarski(esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 1.01/1.19  fof(c_0_23, plain, ![X47]:~v1_xboole_0(k1_zfmisc_1(X47)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 1.01/1.19  cnf(c_0_24, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.01/1.19  cnf(c_0_25, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.01/1.19  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.01/1.19  cnf(c_0_27, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.01/1.19  fof(c_0_28, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_xboole_0(X24,X25)|r1_xboole_0(X23,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 1.01/1.19  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_24])).
% 1.01/1.19  cnf(c_0_30, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 1.01/1.19  fof(c_0_31, plain, ![X29, X30, X31]:(~r1_tarski(X29,X30)|r1_xboole_0(X29,k4_xboole_0(X31,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 1.01/1.19  fof(c_0_32, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.01/1.19  cnf(c_0_33, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.01/1.19  cnf(c_0_34, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.01/1.19  cnf(c_0_35, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.01/1.19  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.01/1.19  cnf(c_0_37, negated_conjecture, (r1_xboole_0(esk4_0,X1)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.01/1.19  cnf(c_0_38, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 1.01/1.19  fof(c_0_39, plain, ![X10]:k3_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 1.01/1.19  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))|~r1_tarski(esk2_0,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.01/1.19  cnf(c_0_41, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.01/1.19  fof(c_0_42, plain, ![X35]:k5_xboole_0(X35,X35)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 1.01/1.19  fof(c_0_43, plain, ![X16, X17]:r1_tarski(k3_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.01/1.19  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(X1,X1))|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.01/1.19  cnf(c_0_45, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.01/1.19  cnf(c_0_46, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.01/1.19  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk4_0,k1_xboole_0)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 1.01/1.19  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_46, c_0_41])).
% 1.01/1.19  fof(c_0_49, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 1.01/1.19  cnf(c_0_50, negated_conjecture, (r1_xboole_0(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.01/1.19  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.01/1.19  cnf(c_0_52, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_50, c_0_45])).
% 1.01/1.19  fof(c_0_53, plain, ![X13, X14, X15]:k5_xboole_0(k3_xboole_0(X13,X14),k3_xboole_0(X15,X14))=k3_xboole_0(k5_xboole_0(X13,X15),X14), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 1.01/1.19  fof(c_0_54, plain, ![X22]:k5_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t5_boole])).
% 1.01/1.19  fof(c_0_55, plain, ![X26, X27, X28]:(~r1_xboole_0(X26,k4_xboole_0(X27,X28))|r1_xboole_0(X27,k4_xboole_0(X26,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 1.01/1.19  cnf(c_0_56, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.01/1.19  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.01/1.19  cnf(c_0_58, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.01/1.19  cnf(c_0_59, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.01/1.19  cnf(c_0_60, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.01/1.19  cnf(c_0_61, negated_conjecture, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k3_xboole_0(esk4_0,k5_xboole_0(X3,X3))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 1.01/1.19  cnf(c_0_62, plain, (k3_xboole_0(k5_xboole_0(X1,X1),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_58])).
% 1.01/1.19  fof(c_0_63, plain, ![X32, X33, X34]:k5_xboole_0(k5_xboole_0(X32,X33),X34)=k5_xboole_0(X32,k5_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 1.01/1.19  cnf(c_0_64, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_59, c_0_45])).
% 1.01/1.19  cnf(c_0_65, plain, (r1_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))|~r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_36]), c_0_36])).
% 1.01/1.19  cnf(c_0_66, negated_conjecture, (r1_xboole_0(k5_xboole_0(X1,X1),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_57])).
% 1.01/1.19  cnf(c_0_67, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.01/1.19  cnf(c_0_68, plain, (k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X2,X2),X3))=X1), inference(spm,[status(thm)],[c_0_64, c_0_58])).
% 1.01/1.19  cnf(c_0_69, negated_conjecture, (r1_xboole_0(X1,k5_xboole_0(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68])).
% 1.01/1.19  fof(c_0_70, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.01/1.19  fof(c_0_71, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 1.01/1.19  cnf(c_0_72, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_41]), c_0_69])])).
% 1.01/1.19  cnf(c_0_73, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.01/1.19  cnf(c_0_74, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.01/1.19  fof(c_0_75, plain, ![X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(X45))|k3_subset_1(X45,X46)=k4_xboole_0(X45,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 1.01/1.19  cnf(c_0_76, negated_conjecture, (r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))|r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.01/1.19  fof(c_0_77, plain, ![X18, X19]:k4_xboole_0(X18,k3_xboole_0(X18,X19))=k4_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 1.01/1.19  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_37, c_0_72])).
% 1.01/1.19  cnf(c_0_79, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_41]), c_0_73])).
% 1.01/1.19  cnf(c_0_80, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_59, c_0_74])).
% 1.01/1.19  cnf(c_0_81, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 1.01/1.19  cnf(c_0_82, negated_conjecture, (k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))=k1_xboole_0|r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_76])).
% 1.01/1.19  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.01/1.19  cnf(c_0_84, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.01/1.19  cnf(c_0_85, negated_conjecture, (r1_xboole_0(esk4_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 1.01/1.19  cnf(c_0_86, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_45]), c_0_80])).
% 1.01/1.19  cnf(c_0_87, negated_conjecture, (~r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))|~r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.01/1.19  cnf(c_0_88, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_81, c_0_36])).
% 1.01/1.19  cnf(c_0_89, negated_conjecture, (k3_xboole_0(k3_subset_1(esk2_0,esk4_0),k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)))=k3_subset_1(esk2_0,esk4_0)|r1_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_82]), c_0_59]), c_0_74])).
% 1.01/1.19  cnf(c_0_90, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_83]), c_0_27])).
% 1.01/1.19  cnf(c_0_91, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_36]), c_0_36])).
% 1.01/1.19  cnf(c_0_92, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_67])).
% 1.01/1.19  cnf(c_0_93, negated_conjecture, (k1_xboole_0=k3_xboole_0(esk4_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_51, c_0_85])).
% 1.01/1.19  cnf(c_0_94, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_86, c_0_74])).
% 1.01/1.19  cnf(c_0_95, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk4_0,esk2_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_26])]), c_0_73])).
% 1.01/1.19  cnf(c_0_96, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_41]), c_0_74]), c_0_73])).
% 1.01/1.19  cnf(c_0_97, plain, (r1_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3)))|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_73]), c_0_79])).
% 1.01/1.19  cnf(c_0_98, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2)))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_86, c_0_79])).
% 1.01/1.19  cnf(c_0_99, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)))=esk3_0|r1_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_89]), c_0_67]), c_0_64]), c_0_67]), c_0_64]), c_0_73])).
% 1.01/1.19  cnf(c_0_100, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_79, c_0_73])).
% 1.01/1.19  cnf(c_0_101, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_80])).
% 1.01/1.19  cnf(c_0_102, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_90])).
% 1.01/1.19  cnf(c_0_103, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_91]), c_0_86])).
% 1.01/1.19  cnf(c_0_104, plain, (k5_xboole_0(X1,X1)=k3_xboole_0(esk4_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 1.01/1.19  cnf(c_0_105, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0)))), inference(rw,[status(thm)],[c_0_95, c_0_96])).
% 1.01/1.19  cnf(c_0_106, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_97, c_0_86])).
% 1.01/1.19  cnf(c_0_107, negated_conjecture, (k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))=k5_xboole_0(esk3_0,esk3_0)|r1_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_73])).
% 1.01/1.19  cnf(c_0_108, plain, (k3_subset_1(X1,X2)=k3_xboole_0(X1,k5_xboole_0(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_88, c_0_100])).
% 1.01/1.19  cnf(c_0_109, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_101])).
% 1.01/1.19  cnf(c_0_110, negated_conjecture, (r1_xboole_0(esk3_0,X1)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_102])).
% 1.01/1.19  cnf(c_0_111, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(esk4_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0)))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_51, c_0_93])).
% 1.01/1.19  cnf(c_0_112, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X1))=k5_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_79, c_0_41])).
% 1.01/1.19  cnf(c_0_113, plain, (k3_xboole_0(esk4_0,k5_xboole_0(X1,X1))=k5_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 1.01/1.19  cnf(c_0_114, negated_conjecture, (k1_xboole_0=k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0)))|r1_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_88]), c_0_26])]), c_0_73]), c_0_96])).
% 1.01/1.19  cnf(c_0_115, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_94])])).
% 1.01/1.19  cnf(c_0_116, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0)))=k5_xboole_0(esk3_0,esk3_0)|r1_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_26])]), c_0_74])).
% 1.01/1.19  cnf(c_0_117, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_109]), c_0_109]), c_0_59]), c_0_59])).
% 1.01/1.19  cnf(c_0_118, negated_conjecture, (r1_xboole_0(X1,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk2_0)))), inference(spm,[status(thm)],[c_0_65, c_0_78])).
% 1.01/1.19  cnf(c_0_119, negated_conjecture, (r1_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_110, c_0_72])).
% 1.01/1.19  cnf(c_0_120, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_112]), c_0_113])).
% 1.01/1.19  cnf(c_0_121, negated_conjecture, (k5_xboole_0(esk2_0,esk2_0)=k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_114, c_0_115]), c_0_93]), c_0_112]), c_0_113])).
% 1.01/1.19  cnf(c_0_122, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0)))=k5_xboole_0(esk3_0,esk3_0)), inference(sr,[status(thm)],[c_0_116, c_0_115])).
% 1.01/1.19  cnf(c_0_123, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk2_0)),X1)), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 1.01/1.19  cnf(c_0_124, negated_conjecture, (r1_xboole_0(X1,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_65, c_0_119])).
% 1.01/1.19  cnf(c_0_125, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(esk3_0,esk3_0)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_121]), c_0_122])).
% 1.01/1.19  cnf(c_0_126, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk2_0)),X1)), inference(rw,[status(thm)],[c_0_123, c_0_100])).
% 1.01/1.19  cnf(c_0_127, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)),X1)), inference(spm,[status(thm)],[c_0_117, c_0_124])).
% 1.01/1.19  cnf(c_0_128, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_46, c_0_73])).
% 1.01/1.19  cnf(c_0_129, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk2_0)),X1)=k5_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 1.01/1.19  cnf(c_0_130, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk2_0)),X1)), inference(rw,[status(thm)],[c_0_127, c_0_100])).
% 1.01/1.19  cnf(c_0_131, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)))|r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_128, c_0_99])).
% 1.01/1.19  cnf(c_0_132, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk2_0))=k5_xboole_0(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_129]), c_0_64]), c_0_129])).
% 1.01/1.19  cnf(c_0_133, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk2_0)),X1)=k5_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_125, c_0_130])).
% 1.01/1.19  cnf(c_0_134, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0))))|r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_88]), c_0_73]), c_0_96]), c_0_26])])).
% 1.01/1.19  cnf(c_0_135, negated_conjecture, (k3_xboole_0(esk4_0,esk2_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_132]), c_0_64]), c_0_86])).
% 1.01/1.19  cnf(c_0_136, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk2_0))=k5_xboole_0(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_133]), c_0_64]), c_0_133])).
% 1.01/1.19  cnf(c_0_137, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0))))), inference(sr,[status(thm)],[c_0_134, c_0_115])).
% 1.01/1.19  cnf(c_0_138, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,esk2_0))=k5_xboole_0(esk4_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_132]), c_0_67]), c_0_64]), c_0_67]), c_0_74]), c_0_86]), c_0_73])).
% 1.01/1.19  cnf(c_0_139, plain, (r1_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_72, c_0_100])).
% 1.01/1.19  cnf(c_0_140, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(X1,esk2_0))=k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_135]), c_0_73])).
% 1.01/1.19  cnf(c_0_141, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_136]), c_0_86]), c_0_86])).
% 1.01/1.19  cnf(c_0_142, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk2_0)))), inference(rw,[status(thm)],[c_0_137, c_0_138])).
% 1.01/1.19  cnf(c_0_143, plain, (r1_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_139, c_0_86])).
% 1.01/1.19  cnf(c_0_144, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,esk4_0))=k5_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_74]), c_0_74])).
% 1.01/1.19  cnf(c_0_145, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_67, c_0_74])).
% 1.01/1.19  cnf(c_0_146, negated_conjecture, (r1_xboole_0(esk3_0,X1)|~r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk2_0)),X1)), inference(spm,[status(thm)],[c_0_33, c_0_142])).
% 1.01/1.19  cnf(c_0_147, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk2_0)),k5_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_145])).
% 1.01/1.19  cnf(c_0_148, negated_conjecture, (r1_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 1.01/1.19  cnf(c_0_149, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk4_0))=k5_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_125, c_0_148])).
% 1.01/1.19  cnf(c_0_150, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_149]), c_0_86]), c_0_86])).
% 1.01/1.19  cnf(c_0_151, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_150]), c_0_115]), ['proof']).
% 1.01/1.19  # SZS output end CNFRefutation
% 1.01/1.19  # Proof object total steps             : 152
% 1.01/1.19  # Proof object clause steps            : 113
% 1.01/1.19  # Proof object formula steps           : 39
% 1.01/1.19  # Proof object conjectures             : 62
% 1.01/1.19  # Proof object clause conjectures      : 59
% 1.01/1.19  # Proof object formula conjectures     : 3
% 1.01/1.19  # Proof object initial clauses used    : 23
% 1.01/1.19  # Proof object initial formulas used   : 19
% 1.01/1.19  # Proof object generating inferences   : 72
% 1.01/1.19  # Proof object simplifying inferences  : 87
% 1.01/1.19  # Training examples: 0 positive, 0 negative
% 1.01/1.19  # Parsed axioms                        : 20
% 1.01/1.19  # Removed by relevancy pruning/SinE    : 0
% 1.01/1.19  # Initial clauses                      : 30
% 1.01/1.19  # Removed in clause preprocessing      : 1
% 1.01/1.19  # Initial clauses in saturation        : 29
% 1.01/1.19  # Processed clauses                    : 10694
% 1.01/1.19  # ...of these trivial                  : 549
% 1.01/1.19  # ...subsumed                          : 8623
% 1.01/1.19  # ...remaining for further processing  : 1522
% 1.01/1.19  # Other redundant clauses eliminated   : 23
% 1.01/1.19  # Clauses deleted for lack of memory   : 0
% 1.01/1.19  # Backward-subsumed                    : 117
% 1.01/1.19  # Backward-rewritten                   : 413
% 1.01/1.19  # Generated clauses                    : 78210
% 1.01/1.19  # ...of the previous two non-trivial   : 65682
% 1.01/1.19  # Contextual simplify-reflections      : 0
% 1.01/1.19  # Paramodulations                      : 78045
% 1.01/1.19  # Factorizations                       : 50
% 1.01/1.19  # Equation resolutions                 : 37
% 1.01/1.19  # Propositional unsat checks           : 0
% 1.01/1.19  #    Propositional check models        : 0
% 1.01/1.19  #    Propositional check unsatisfiable : 0
% 1.01/1.19  #    Propositional clauses             : 0
% 1.01/1.19  #    Propositional clauses after purity: 0
% 1.01/1.19  #    Propositional unsat core size     : 0
% 1.01/1.19  #    Propositional preprocessing time  : 0.000
% 1.01/1.19  #    Propositional encoding time       : 0.000
% 1.01/1.19  #    Propositional solver time         : 0.000
% 1.01/1.19  #    Success case prop preproc time    : 0.000
% 1.01/1.19  #    Success case prop encoding time   : 0.000
% 1.01/1.19  #    Success case prop solver time     : 0.000
% 1.01/1.19  # Current number of processed clauses  : 883
% 1.01/1.19  #    Positive orientable unit clauses  : 202
% 1.01/1.19  #    Positive unorientable unit clauses: 31
% 1.01/1.19  #    Negative unit clauses             : 2
% 1.01/1.19  #    Non-unit-clauses                  : 648
% 1.01/1.19  # Current number of unprocessed clauses: 52154
% 1.01/1.19  # ...number of literals in the above   : 105527
% 1.01/1.19  # Current number of archived formulas  : 0
% 1.01/1.19  # Current number of archived clauses   : 638
% 1.01/1.19  # Clause-clause subsumption calls (NU) : 236029
% 1.01/1.19  # Rec. Clause-clause subsumption calls : 208819
% 1.01/1.19  # Non-unit clause-clause subsumptions  : 7827
% 1.01/1.19  # Unit Clause-clause subsumption calls : 5096
% 1.01/1.19  # Rewrite failures with RHS unbound    : 924
% 1.01/1.19  # BW rewrite match attempts            : 2462
% 1.01/1.19  # BW rewrite match successes           : 683
% 1.01/1.19  # Condensation attempts                : 0
% 1.01/1.19  # Condensation successes               : 0
% 1.01/1.19  # Termbank termtop insertions          : 1268849
% 1.01/1.20  
% 1.01/1.20  # -------------------------------------------------
% 1.01/1.20  # User time                : 0.805 s
% 1.01/1.20  # System time              : 0.033 s
% 1.01/1.20  # Total time               : 0.838 s
% 1.01/1.20  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
