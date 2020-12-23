%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:37 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :  150 (8735 expanded)
%              Number of clauses        :  109 (4049 expanded)
%              Number of leaves         :   20 (2286 expanded)
%              Depth                    :   23
%              Number of atoms          :  286 (14992 expanded)
%              Number of equality atoms :   75 (6302 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(c_0_20,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r1_xboole_0(X8,X9)
        | r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X13,k3_xboole_0(X11,X12))
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | r1_tarski(k3_xboole_0(X20,X22),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

fof(c_0_26,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_27,plain,(
    ! [X44,X45,X46,X47,X48,X49] :
      ( ( ~ r2_hidden(X46,X45)
        | r1_tarski(X46,X44)
        | X45 != k1_zfmisc_1(X44) )
      & ( ~ r1_tarski(X47,X44)
        | r2_hidden(X47,X45)
        | X45 != k1_zfmisc_1(X44) )
      & ( ~ r2_hidden(esk3_2(X48,X49),X49)
        | ~ r1_tarski(esk3_2(X48,X49),X48)
        | X49 = k1_zfmisc_1(X48) )
      & ( r2_hidden(esk3_2(X48,X49),X49)
        | r1_tarski(esk3_2(X48,X49),X48)
        | X49 = k1_zfmisc_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_28,plain,(
    ! [X51,X52] :
      ( ( ~ m1_subset_1(X52,X51)
        | r2_hidden(X52,X51)
        | v1_xboole_0(X51) )
      & ( ~ r2_hidden(X52,X51)
        | m1_subset_1(X52,X51)
        | v1_xboole_0(X51) )
      & ( ~ m1_subset_1(X52,X51)
        | v1_xboole_0(X52)
        | ~ v1_xboole_0(X51) )
      & ( ~ v1_xboole_0(X52)
        | m1_subset_1(X52,X51)
        | ~ v1_xboole_0(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))
    & ( ~ r1_tarski(esk5_0,esk6_0)
      | ~ r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) )
    & ( r1_tarski(esk5_0,esk6_0)
      | r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_30,plain,(
    ! [X55] : ~ v1_xboole_0(k1_zfmisc_1(X55)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_31,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(X1,X4))
    | ~ r1_xboole_0(k3_xboole_0(X1,X4),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

fof(c_0_42,plain,(
    ! [X26,X27] : r1_tarski(k4_xboole_0(X26,X27),X26) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_43,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_44,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ r2_hidden(X4,X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_48,plain,(
    ! [X37,X38] : r1_xboole_0(k4_xboole_0(X37,X38),X38) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_49,plain,(
    ! [X33] : k4_xboole_0(k1_xboole_0,X33) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_50,plain,(
    ! [X31,X32] : k4_xboole_0(X31,k4_xboole_0(X31,X32)) = k3_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(X1,esk6_0)
    | ~ r2_hidden(X2,X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_56,plain,(
    ! [X23] : k2_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_57,plain,(
    ! [X42,X43] : k2_xboole_0(X42,X43) = k5_xboole_0(X42,k4_xboole_0(X43,X42)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(X1,k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X2)))
    | ~ r1_xboole_0(k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X2)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_47])).

fof(c_0_60,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_47])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_47]),c_0_47])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_65,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_66,plain,(
    ! [X53,X54] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(X53))
      | k3_subset_1(X53,X54) = k4_xboole_0(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(X1,k5_xboole_0(esk6_0,k3_xboole_0(esk4_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_33])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_47])).

cnf(c_0_71,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_39])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_69])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_70,c_0_61])).

cnf(c_0_79,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_33])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_72]),c_0_37])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_83,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_47])).

cnf(c_0_84,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_78]),c_0_79])])).

cnf(c_0_85,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_81])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_82])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_62])).

cnf(c_0_90,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_39])).

cnf(c_0_91,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk6_0) = k3_subset_1(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_36])])).

cnf(c_0_92,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_37])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_39]),c_0_52])])).

cnf(c_0_94,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_39])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_tarski(X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_87])).

cnf(c_0_96,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_68])).

cnf(c_0_97,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_98,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_77]),c_0_77]),c_0_78]),c_0_78])).

cnf(c_0_99,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_68])).

cnf(c_0_100,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_45])])).

fof(c_0_101,plain,(
    ! [X39,X40,X41] :
      ( ~ r1_tarski(X39,X40)
      | ~ r1_xboole_0(X39,X41)
      | r1_tarski(X39,k4_xboole_0(X40,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_39]),c_0_92])).

cnf(c_0_103,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_subset_1(esk4_0,esk6_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_84]),c_0_91])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_91]),c_0_45])])).

cnf(c_0_105,negated_conjecture,
    ( ~ r2_hidden(X1,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X2)))
    | ~ r1_xboole_0(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X2)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_52])).

cnf(c_0_106,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])).

cnf(c_0_107,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_33])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_109,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X2))) = k3_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_83])).

cnf(c_0_110,negated_conjecture,
    ( k3_subset_1(esk4_0,k3_subset_1(esk4_0,esk6_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])])).

cnf(c_0_111,negated_conjecture,
    ( ~ r2_hidden(X1,k5_xboole_0(esk5_0,k3_xboole_0(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_59]),c_0_33])).

cnf(c_0_112,plain,
    ( X1 = k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0))
    | r2_hidden(esk1_2(X1,X1),X1) ),
    inference(rw,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_113,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_108,c_0_47])).

cnf(c_0_114,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_subset_1(esk4_0,esk6_0)) = k3_subset_1(esk4_0,esk6_0)
    | ~ m1_subset_1(k3_subset_1(esk4_0,esk6_0),k1_zfmisc_1(esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_84]),c_0_91])).

fof(c_0_115,plain,(
    ! [X34,X35,X36] :
      ( ~ r1_tarski(X34,X35)
      | ~ r1_xboole_0(X35,X36)
      | r1_xboole_0(X34,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_116,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk4_0,esk5_0)) = k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_117,plain,
    ( k3_xboole_0(X1,k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0))) = k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_107]),c_0_107])).

cnf(c_0_118,plain,
    ( k5_xboole_0(X1,k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_78,c_0_107])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(esk5_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)))
    | ~ r1_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_87])).

cnf(c_0_120,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_subset_1(esk4_0,esk6_0)) = k3_subset_1(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_92]),c_0_104])])).

cnf(c_0_121,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    | r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_123,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_116]),c_0_117]),c_0_118]),c_0_79])])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    | ~ r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_103])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    | r1_xboole_0(k3_subset_1(esk4_0,esk6_0),X1)
    | ~ r1_xboole_0(k3_subset_1(esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_126,plain,
    ( r1_xboole_0(k3_subset_1(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_83])).

cnf(c_0_127,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk5_0) = k3_subset_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_123]),c_0_72])])).

cnf(c_0_128,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    | r2_hidden(esk1_2(esk5_0,k3_subset_1(esk4_0,esk6_0)),k3_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_124,c_0_97])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    | r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_72])])).

cnf(c_0_131,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_99,c_0_107])).

cnf(c_0_132,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_127]),c_0_87])])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_130])).

cnf(c_0_134,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_62])).

cnf(c_0_135,negated_conjecture,
    ( k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0)) = k3_xboole_0(esk5_0,k3_subset_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_33])).

cnf(c_0_136,negated_conjecture,
    ( r1_xboole_0(esk5_0,X1)
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( r1_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_84]),c_0_91])).

cnf(c_0_138,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X3)))
    | ~ r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_113,c_0_52])).

cnf(c_0_139,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(esk5_0,k3_subset_1(esk4_0,esk5_0))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_131,c_0_135])).

cnf(c_0_140,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_141,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk6_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)))
    | ~ r1_xboole_0(k3_subset_1(esk4_0,esk6_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_84]),c_0_91]),c_0_91])).

cnf(c_0_142,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_33])).

cnf(c_0_143,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0)) = k3_xboole_0(esk5_0,k3_subset_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_144,plain,
    ( k5_xboole_0(X1,k3_xboole_0(esk5_0,k3_subset_1(esk4_0,esk5_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_118,c_0_135])).

cnf(c_0_145,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk6_0)
    | ~ r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_146,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))
    | ~ r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_123]),c_0_127])).

cnf(c_0_147,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_144])).

cnf(c_0_148,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_145,c_0_133])])).

cnf(c_0_149,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_146,c_0_147])]),c_0_148]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 7.15/7.36  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 7.15/7.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 7.15/7.36  #
% 7.15/7.36  # Preprocessing time       : 0.028 s
% 7.15/7.36  # Presaturation interreduction done
% 7.15/7.36  
% 7.15/7.36  # Proof found!
% 7.15/7.36  # SZS status Theorem
% 7.15/7.36  # SZS output start CNFRefutation
% 7.15/7.36  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.15/7.36  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.15/7.36  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 7.15/7.36  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 7.15/7.36  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.15/7.36  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 7.15/7.36  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 7.15/7.36  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 7.15/7.36  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.15/7.36  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.15/7.36  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.15/7.36  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 7.15/7.36  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.15/7.36  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 7.15/7.36  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.15/7.36  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.15/7.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.15/7.36  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 7.15/7.36  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 7.15/7.36  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 7.15/7.36  fof(c_0_20, plain, ![X8, X9, X11, X12, X13]:((r1_xboole_0(X8,X9)|r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)))&(~r2_hidden(X13,k3_xboole_0(X11,X12))|~r1_xboole_0(X11,X12))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 7.15/7.36  fof(c_0_21, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 7.15/7.36  fof(c_0_22, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 7.15/7.36  cnf(c_0_23, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 7.15/7.36  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.15/7.36  fof(c_0_25, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|r1_tarski(k3_xboole_0(X20,X22),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 7.15/7.36  fof(c_0_26, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 7.15/7.36  fof(c_0_27, plain, ![X44, X45, X46, X47, X48, X49]:(((~r2_hidden(X46,X45)|r1_tarski(X46,X44)|X45!=k1_zfmisc_1(X44))&(~r1_tarski(X47,X44)|r2_hidden(X47,X45)|X45!=k1_zfmisc_1(X44)))&((~r2_hidden(esk3_2(X48,X49),X49)|~r1_tarski(esk3_2(X48,X49),X48)|X49=k1_zfmisc_1(X48))&(r2_hidden(esk3_2(X48,X49),X49)|r1_tarski(esk3_2(X48,X49),X48)|X49=k1_zfmisc_1(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 7.15/7.36  fof(c_0_28, plain, ![X51, X52]:(((~m1_subset_1(X52,X51)|r2_hidden(X52,X51)|v1_xboole_0(X51))&(~r2_hidden(X52,X51)|m1_subset_1(X52,X51)|v1_xboole_0(X51)))&((~m1_subset_1(X52,X51)|v1_xboole_0(X52)|~v1_xboole_0(X51))&(~v1_xboole_0(X52)|m1_subset_1(X52,X51)|~v1_xboole_0(X51)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 7.15/7.36  fof(c_0_29, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))&((~r1_tarski(esk5_0,esk6_0)|~r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)))&(r1_tarski(esk5_0,esk6_0)|r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 7.15/7.36  fof(c_0_30, plain, ![X55]:~v1_xboole_0(k1_zfmisc_1(X55)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 7.15/7.36  cnf(c_0_31, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 7.15/7.36  cnf(c_0_32, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 7.15/7.36  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 7.15/7.36  cnf(c_0_34, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 7.15/7.36  cnf(c_0_35, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 7.15/7.36  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 7.15/7.36  cnf(c_0_37, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 7.15/7.36  cnf(c_0_38, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,k3_xboole_0(X1,X4))|~r1_xboole_0(k3_xboole_0(X1,X4),X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 7.15/7.36  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_33])).
% 7.15/7.36  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_34])).
% 7.15/7.36  cnf(c_0_41, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 7.15/7.36  fof(c_0_42, plain, ![X26, X27]:r1_tarski(k4_xboole_0(X26,X27),X26), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 7.15/7.36  fof(c_0_43, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 7.15/7.36  cnf(c_0_44, plain, (~r1_tarski(X1,X2)|~r1_tarski(X3,X1)|~r2_hidden(X4,X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 7.15/7.36  cnf(c_0_45, negated_conjecture, (r1_tarski(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 7.15/7.36  cnf(c_0_46, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 7.15/7.36  cnf(c_0_47, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 7.15/7.36  fof(c_0_48, plain, ![X37, X38]:r1_xboole_0(k4_xboole_0(X37,X38),X38), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 7.15/7.36  fof(c_0_49, plain, ![X33]:k4_xboole_0(k1_xboole_0,X33)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 7.15/7.36  fof(c_0_50, plain, ![X31, X32]:k4_xboole_0(X31,k4_xboole_0(X31,X32))=k3_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 7.15/7.36  cnf(c_0_51, negated_conjecture, (~r1_tarski(X1,esk6_0)|~r2_hidden(X2,X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 7.15/7.36  cnf(c_0_52, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 7.15/7.36  cnf(c_0_53, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 7.15/7.36  cnf(c_0_54, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 7.15/7.36  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 7.15/7.36  fof(c_0_56, plain, ![X23]:k2_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t1_boole])).
% 7.15/7.36  fof(c_0_57, plain, ![X42, X43]:k2_xboole_0(X42,X43)=k5_xboole_0(X42,k4_xboole_0(X43,X42)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 7.15/7.36  cnf(c_0_58, negated_conjecture, (~r2_hidden(X1,k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X2)))|~r1_xboole_0(k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X2)),esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 7.15/7.36  cnf(c_0_59, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_53, c_0_47])).
% 7.15/7.36  fof(c_0_60, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 7.15/7.36  cnf(c_0_61, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_54, c_0_47])).
% 7.15/7.36  cnf(c_0_62, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_47]), c_0_47])).
% 7.15/7.36  cnf(c_0_63, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 7.15/7.36  cnf(c_0_64, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 7.15/7.36  fof(c_0_65, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 7.15/7.36  fof(c_0_66, plain, ![X53, X54]:(~m1_subset_1(X54,k1_zfmisc_1(X53))|k3_subset_1(X53,X54)=k4_xboole_0(X53,X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 7.15/7.36  cnf(c_0_67, negated_conjecture, (~r2_hidden(X1,k5_xboole_0(esk6_0,k3_xboole_0(esk4_0,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_33])).
% 7.15/7.36  cnf(c_0_68, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 7.15/7.36  cnf(c_0_69, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 7.15/7.36  cnf(c_0_70, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_47])).
% 7.15/7.36  cnf(c_0_71, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_52, c_0_62])).
% 7.15/7.36  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 7.15/7.36  cnf(c_0_73, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_65])).
% 7.15/7.36  cnf(c_0_74, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 7.15/7.36  cnf(c_0_75, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2)))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_62, c_0_39])).
% 7.15/7.36  cnf(c_0_76, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk4_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 7.15/7.36  cnf(c_0_77, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_69])).
% 7.15/7.36  cnf(c_0_78, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_70, c_0_61])).
% 7.15/7.36  cnf(c_0_79, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_71, c_0_33])).
% 7.15/7.36  cnf(c_0_80, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 7.15/7.36  cnf(c_0_81, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_72]), c_0_37])).
% 7.15/7.36  cnf(c_0_82, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_73])).
% 7.15/7.36  cnf(c_0_83, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_74, c_0_47])).
% 7.15/7.36  cnf(c_0_84, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_78]), c_0_79])])).
% 7.15/7.36  cnf(c_0_85, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 7.15/7.36  cnf(c_0_86, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_80])).
% 7.15/7.36  cnf(c_0_87, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_81])).
% 7.15/7.36  cnf(c_0_88, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_31, c_0_82])).
% 7.15/7.36  cnf(c_0_89, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_62, c_0_62])).
% 7.15/7.36  cnf(c_0_90, plain, (r1_xboole_0(k5_xboole_0(X1,X2),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_59, c_0_39])).
% 7.15/7.36  cnf(c_0_91, negated_conjecture, (k5_xboole_0(esk4_0,esk6_0)=k3_subset_1(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_36])])).
% 7.15/7.36  cnf(c_0_92, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_37])).
% 7.15/7.36  cnf(c_0_93, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_39]), c_0_52])])).
% 7.15/7.36  cnf(c_0_94, plain, (r1_tarski(k5_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_52, c_0_39])).
% 7.15/7.36  cnf(c_0_95, negated_conjecture, (~r1_tarski(X1,esk5_0)|~r2_hidden(X2,X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_87])).
% 7.15/7.36  cnf(c_0_96, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_88, c_0_68])).
% 7.15/7.36  cnf(c_0_97, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 7.15/7.36  cnf(c_0_98, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_77]), c_0_77]), c_0_78]), c_0_78])).
% 7.15/7.36  cnf(c_0_99, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_68])).
% 7.15/7.36  cnf(c_0_100, negated_conjecture, (r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_45])])).
% 7.15/7.36  fof(c_0_101, plain, ![X39, X40, X41]:(~r1_tarski(X39,X40)|~r1_xboole_0(X39,X41)|r1_tarski(X39,k4_xboole_0(X40,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 7.15/7.36  cnf(c_0_102, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_39]), c_0_92])).
% 7.15/7.36  cnf(c_0_103, negated_conjecture, (k5_xboole_0(esk4_0,k3_subset_1(esk4_0,esk6_0))=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_84]), c_0_91])).
% 7.15/7.36  cnf(c_0_104, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk6_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_91]), c_0_45])])).
% 7.15/7.36  cnf(c_0_105, negated_conjecture, (~r2_hidden(X1,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X2)))|~r1_xboole_0(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X2)),esk4_0)), inference(spm,[status(thm)],[c_0_95, c_0_52])).
% 7.15/7.36  cnf(c_0_106, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])).
% 7.15/7.36  cnf(c_0_107, negated_conjecture, (k1_xboole_0=k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_33])).
% 7.15/7.36  cnf(c_0_108, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 7.15/7.36  cnf(c_0_109, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X2)))=k3_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_83])).
% 7.15/7.36  cnf(c_0_110, negated_conjecture, (k3_subset_1(esk4_0,k3_subset_1(esk4_0,esk6_0))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104])])).
% 7.15/7.36  cnf(c_0_111, negated_conjecture, (~r2_hidden(X1,k5_xboole_0(esk5_0,k3_xboole_0(esk4_0,esk5_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_59]), c_0_33])).
% 7.15/7.36  cnf(c_0_112, plain, (X1=k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0))|r2_hidden(esk1_2(X1,X1),X1)), inference(rw,[status(thm)],[c_0_106, c_0_107])).
% 7.15/7.36  cnf(c_0_113, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_108, c_0_47])).
% 7.15/7.36  cnf(c_0_114, negated_conjecture, (k3_xboole_0(esk4_0,k3_subset_1(esk4_0,esk6_0))=k3_subset_1(esk4_0,esk6_0)|~m1_subset_1(k3_subset_1(esk4_0,esk6_0),k1_zfmisc_1(esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_84]), c_0_91])).
% 7.15/7.36  fof(c_0_115, plain, ![X34, X35, X36]:(~r1_tarski(X34,X35)|~r1_xboole_0(X35,X36)|r1_xboole_0(X34,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 7.15/7.36  cnf(c_0_116, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk4_0,esk5_0))=k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 7.15/7.36  cnf(c_0_117, plain, (k3_xboole_0(X1,k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0)))=k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_107]), c_0_107])).
% 7.15/7.36  cnf(c_0_118, plain, (k5_xboole_0(X1,k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0)))=X1), inference(rw,[status(thm)],[c_0_78, c_0_107])).
% 7.15/7.36  cnf(c_0_119, negated_conjecture, (r1_tarski(esk5_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)))|~r1_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_113, c_0_87])).
% 7.15/7.36  cnf(c_0_120, negated_conjecture, (k3_xboole_0(esk4_0,k3_subset_1(esk4_0,esk6_0))=k3_subset_1(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_92]), c_0_104])])).
% 7.15/7.36  cnf(c_0_121, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 7.15/7.36  cnf(c_0_122, negated_conjecture, (r1_tarski(esk5_0,esk6_0)|r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 7.15/7.36  cnf(c_0_123, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_116]), c_0_117]), c_0_118]), c_0_79])])).
% 7.15/7.36  cnf(c_0_124, negated_conjecture, (r1_tarski(esk5_0,esk6_0)|~r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_103])).
% 7.15/7.36  cnf(c_0_125, negated_conjecture, (r1_tarski(esk5_0,esk6_0)|r1_xboole_0(k3_subset_1(esk4_0,esk6_0),X1)|~r1_xboole_0(k3_subset_1(esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 7.15/7.36  cnf(c_0_126, plain, (r1_xboole_0(k3_subset_1(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_83])).
% 7.15/7.36  cnf(c_0_127, negated_conjecture, (k5_xboole_0(esk4_0,esk5_0)=k3_subset_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_123]), c_0_72])])).
% 7.15/7.36  cnf(c_0_128, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 7.15/7.36  cnf(c_0_129, negated_conjecture, (r1_tarski(esk5_0,esk6_0)|r2_hidden(esk1_2(esk5_0,k3_subset_1(esk4_0,esk6_0)),k3_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_124, c_0_97])).
% 7.15/7.36  cnf(c_0_130, negated_conjecture, (r1_tarski(esk5_0,esk6_0)|r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_72])])).
% 7.15/7.36  cnf(c_0_131, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_99, c_0_107])).
% 7.15/7.36  cnf(c_0_132, negated_conjecture, (r1_xboole_0(k3_subset_1(esk4_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_127]), c_0_87])])).
% 7.15/7.36  cnf(c_0_133, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_130])).
% 7.15/7.36  cnf(c_0_134, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_59, c_0_62])).
% 7.15/7.36  cnf(c_0_135, negated_conjecture, (k3_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0))=k3_xboole_0(esk5_0,k3_subset_1(esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_33])).
% 7.15/7.36  cnf(c_0_136, negated_conjecture, (r1_xboole_0(esk5_0,X1)|~r1_xboole_0(esk6_0,X1)), inference(spm,[status(thm)],[c_0_121, c_0_133])).
% 7.15/7.36  cnf(c_0_137, negated_conjecture, (r1_xboole_0(esk6_0,k3_subset_1(esk4_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_84]), c_0_91])).
% 7.15/7.36  cnf(c_0_138, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X3)))|~r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_113, c_0_52])).
% 7.15/7.36  cnf(c_0_139, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(esk5_0,k3_subset_1(esk4_0,esk5_0))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_131, c_0_135])).
% 7.15/7.36  cnf(c_0_140, negated_conjecture, (r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_136, c_0_137])).
% 7.15/7.36  cnf(c_0_141, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk6_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)))|~r1_xboole_0(k3_subset_1(esk4_0,esk6_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_84]), c_0_91]), c_0_91])).
% 7.15/7.36  cnf(c_0_142, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2)), inference(spm,[status(thm)],[c_0_59, c_0_33])).
% 7.15/7.36  cnf(c_0_143, negated_conjecture, (k3_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))=k3_xboole_0(esk5_0,k3_subset_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 7.15/7.36  cnf(c_0_144, plain, (k5_xboole_0(X1,k3_xboole_0(esk5_0,k3_subset_1(esk4_0,esk5_0)))=X1), inference(rw,[status(thm)],[c_0_118, c_0_135])).
% 7.15/7.36  cnf(c_0_145, negated_conjecture, (~r1_tarski(esk5_0,esk6_0)|~r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 7.15/7.36  cnf(c_0_146, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))|~r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_123]), c_0_127])).
% 7.15/7.36  cnf(c_0_147, negated_conjecture, (r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_144])).
% 7.15/7.36  cnf(c_0_148, negated_conjecture, (~r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_145, c_0_133])])).
% 7.15/7.36  cnf(c_0_149, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_146, c_0_147])]), c_0_148]), ['proof']).
% 7.15/7.36  # SZS output end CNFRefutation
% 7.15/7.36  # Proof object total steps             : 150
% 7.15/7.36  # Proof object clause steps            : 109
% 7.15/7.36  # Proof object formula steps           : 41
% 7.15/7.36  # Proof object conjectures             : 47
% 7.15/7.36  # Proof object clause conjectures      : 44
% 7.15/7.36  # Proof object formula conjectures     : 3
% 7.15/7.36  # Proof object initial clauses used    : 26
% 7.15/7.36  # Proof object initial formulas used   : 20
% 7.15/7.36  # Proof object generating inferences   : 64
% 7.15/7.36  # Proof object simplifying inferences  : 73
% 7.15/7.36  # Training examples: 0 positive, 0 negative
% 7.15/7.36  # Parsed axioms                        : 22
% 7.15/7.36  # Removed by relevancy pruning/SinE    : 0
% 7.15/7.36  # Initial clauses                      : 34
% 7.15/7.36  # Removed in clause preprocessing      : 2
% 7.15/7.36  # Initial clauses in saturation        : 32
% 7.15/7.36  # Processed clauses                    : 40982
% 7.15/7.36  # ...of these trivial                  : 758
% 7.15/7.36  # ...subsumed                          : 36100
% 7.15/7.36  # ...remaining for further processing  : 4124
% 7.15/7.36  # Other redundant clauses eliminated   : 4
% 7.15/7.36  # Clauses deleted for lack of memory   : 0
% 7.15/7.36  # Backward-subsumed                    : 378
% 7.15/7.36  # Backward-rewritten                   : 516
% 7.15/7.36  # Generated clauses                    : 764230
% 7.15/7.36  # ...of the previous two non-trivial   : 691633
% 7.15/7.36  # Contextual simplify-reflections      : 102
% 7.15/7.36  # Paramodulations                      : 764202
% 7.15/7.36  # Factorizations                       : 24
% 7.15/7.36  # Equation resolutions                 : 4
% 7.15/7.36  # Propositional unsat checks           : 0
% 7.15/7.36  #    Propositional check models        : 0
% 7.15/7.36  #    Propositional check unsatisfiable : 0
% 7.15/7.36  #    Propositional clauses             : 0
% 7.15/7.36  #    Propositional clauses after purity: 0
% 7.15/7.36  #    Propositional unsat core size     : 0
% 7.15/7.36  #    Propositional preprocessing time  : 0.000
% 7.15/7.36  #    Propositional encoding time       : 0.000
% 7.15/7.36  #    Propositional solver time         : 0.000
% 7.15/7.36  #    Success case prop preproc time    : 0.000
% 7.15/7.36  #    Success case prop encoding time   : 0.000
% 7.15/7.36  #    Success case prop solver time     : 0.000
% 7.15/7.36  # Current number of processed clauses  : 3195
% 7.15/7.36  #    Positive orientable unit clauses  : 246
% 7.15/7.36  #    Positive unorientable unit clauses: 9
% 7.15/7.36  #    Negative unit clauses             : 177
% 7.15/7.36  #    Non-unit-clauses                  : 2763
% 7.15/7.36  # Current number of unprocessed clauses: 643975
% 7.15/7.36  # ...number of literals in the above   : 2417978
% 7.15/7.36  # Current number of archived formulas  : 0
% 7.15/7.36  # Current number of archived clauses   : 927
% 7.15/7.36  # Clause-clause subsumption calls (NU) : 2254940
% 7.15/7.36  # Rec. Clause-clause subsumption calls : 989807
% 7.15/7.36  # Non-unit clause-clause subsumptions  : 14591
% 7.15/7.36  # Unit Clause-clause subsumption calls : 47839
% 7.15/7.36  # Rewrite failures with RHS unbound    : 62
% 7.15/7.36  # BW rewrite match attempts            : 1973
% 7.15/7.36  # BW rewrite match successes           : 156
% 7.15/7.36  # Condensation attempts                : 0
% 7.15/7.36  # Condensation successes               : 0
% 7.15/7.36  # Termbank termtop insertions          : 21723680
% 7.21/7.39  
% 7.21/7.39  # -------------------------------------------------
% 7.21/7.39  # User time                : 6.759 s
% 7.21/7.39  # System time              : 0.283 s
% 7.21/7.39  # Total time               : 7.042 s
% 7.21/7.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
