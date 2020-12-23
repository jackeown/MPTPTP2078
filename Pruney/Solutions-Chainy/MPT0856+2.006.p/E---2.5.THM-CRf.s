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
% DateTime   : Thu Dec  3 10:59:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 283 expanded)
%              Number of clauses        :   53 ( 119 expanded)
%              Number of leaves         :   23 (  78 expanded)
%              Depth                    :   16
%              Number of atoms          :  205 ( 463 expanded)
%              Number of equality atoms :   52 ( 207 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
       => ( k1_mcart_1(X1) = X2
          & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t12_mcart_1])).

fof(c_0_24,negated_conjecture,
    ( r2_hidden(esk5_0,k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))
    & ( k1_mcart_1(esk5_0) != esk6_0
      | ~ r2_hidden(k2_mcart_1(esk5_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_25,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X25,X26,X27] : k2_enumset1(X25,X25,X26,X27) = k1_enumset1(X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X28,X29,X30,X31] : k3_enumset1(X28,X28,X29,X30,X31) = k2_enumset1(X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,k2_zfmisc_1(X33,X34))
      | k4_tarski(esk3_1(X32),esk4_1(X32)) = X32 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_0,k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X61,X62] :
      ( k1_mcart_1(k4_tarski(X61,X62)) = X61
      & k2_mcart_1(k4_tarski(X61,X62)) = X62 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_36,plain,
    ( k4_tarski(esk3_1(X1),esk4_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_0,k2_zfmisc_1(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_38,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k4_tarski(esk3_1(esk5_0),esk4_1(esk5_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( esk3_1(esk5_0) = k1_mcart_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_41,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk5_0),esk4_1(esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_43,plain,(
    ! [X50] : m1_subset_1(k2_subset_1(X50),k1_zfmisc_1(X50)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_44,plain,(
    ! [X49] : k2_subset_1(X49) = X49 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_45,plain,(
    ! [X39,X40,X41,X42] :
      ( ( r2_hidden(X39,X41)
        | ~ r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) )
      & ( r2_hidden(X40,X42)
        | ~ r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) )
      & ( ~ r2_hidden(X39,X41)
        | ~ r2_hidden(X40,X42)
        | r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_46,negated_conjecture,
    ( esk4_1(esk5_0) = k2_mcart_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_47,plain,(
    ! [X54,X55] :
      ( ~ m1_subset_1(X54,X55)
      | v1_xboole_0(X55)
      | r2_hidden(X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_48,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_50,plain,(
    ! [X51] : ~ v1_xboole_0(k1_zfmisc_1(X51)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_51,plain,(
    ! [X12,X13,X15,X16,X17] :
      ( ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_xboole_0(X12,X13) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | r1_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | ~ r1_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_52,plain,(
    ! [X44,X45,X46,X47] :
      ( ( ~ r1_xboole_0(X44,X45)
        | r1_xboole_0(k2_zfmisc_1(X44,X46),k2_zfmisc_1(X45,X47)) )
      & ( ~ r1_xboole_0(X46,X47)
        | r1_xboole_0(k2_zfmisc_1(X44,X46),k2_zfmisc_1(X45,X47)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_53,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_46])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_58,plain,(
    ! [X58,X59,X60] :
      ( ( r2_hidden(k1_mcart_1(X58),X59)
        | ~ r2_hidden(X58,k2_zfmisc_1(X59,X60)) )
      & ( r2_hidden(k2_mcart_1(X58),X60)
        | ~ r2_hidden(X58,k2_zfmisc_1(X59,X60)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk5_0,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(k2_mcart_1(esk5_0),X2)
    | ~ r2_hidden(k1_mcart_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

fof(c_0_63,plain,(
    ! [X37,X38] :
      ( ( k4_xboole_0(k1_tarski(X37),X38) != k1_tarski(X37)
        | ~ r2_hidden(X37,X38) )
      & ( r2_hidden(X37,X38)
        | k4_xboole_0(k1_tarski(X37),X38) = k1_tarski(X37) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

fof(c_0_64,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_65,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_66,plain,(
    ! [X48] : k3_tarski(k1_tarski(X48)) = X48 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

cnf(c_0_67,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X5)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk5_0,k2_zfmisc_1(X1,k1_zfmisc_1(k2_mcart_1(esk5_0))))
    | ~ r2_hidden(k1_mcart_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_69,plain,(
    ! [X20,X21] :
      ( ( ~ r1_xboole_0(X20,X21)
        | k4_xboole_0(X20,X21) = X20 )
      & ( k4_xboole_0(X20,X21) != X20
        | r1_xboole_0(X20,X21) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_71,plain,(
    ! [X56,X57] :
      ( ( ~ m1_subset_1(X56,k1_zfmisc_1(X57))
        | r1_tarski(X56,X57) )
      & ( ~ r1_tarski(X56,X57)
        | m1_subset_1(X56,k1_zfmisc_1(X57)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_72,plain,(
    ! [X52,X53] :
      ( ~ r2_hidden(X52,X53)
      | m1_subset_1(X52,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_73,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_37])).

fof(c_0_75,plain,(
    ! [X43] : r1_tarski(X43,k1_zfmisc_1(k3_tarski(X43))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

cnf(c_0_76,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk5_0,k2_zfmisc_1(X1,X3))
    | ~ r2_hidden(k1_mcart_1(esk5_0),X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) = k3_enumset1(X1,X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk5_0),X1)
    | ~ r1_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_85,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),X1)
    | ~ r2_hidden(k1_mcart_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_37])).

cnf(c_0_87,plain,
    ( r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

fof(c_0_88,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk5_0),k1_zfmisc_1(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( k1_mcart_1(esk5_0) != esk6_0
    | ~ r2_hidden(k2_mcart_1(esk5_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk5_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_37])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | ~ r2_hidden(k1_mcart_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_94,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k1_mcart_1(esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( k1_mcart_1(esk5_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(k1_mcart_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_62])).

cnf(c_0_98,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k1_mcart_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_97]),c_0_98]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.43  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.028 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t12_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.20/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.43  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.20/0.43  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.20/0.43  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.43  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.43  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.20/0.43  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.43  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.43  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.43  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.20/0.43  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.20/0.43  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.20/0.43  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.43  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.43  fof(t100_zfmisc_1, axiom, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.20/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.43  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3)))), inference(assume_negation,[status(cth)],[t12_mcart_1])).
% 0.20/0.43  fof(c_0_24, negated_conjecture, (r2_hidden(esk5_0,k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))&(k1_mcart_1(esk5_0)!=esk6_0|~r2_hidden(k2_mcart_1(esk5_0),esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.20/0.43  fof(c_0_25, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.43  fof(c_0_26, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.43  fof(c_0_27, plain, ![X25, X26, X27]:k2_enumset1(X25,X25,X26,X27)=k1_enumset1(X25,X26,X27), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.43  fof(c_0_28, plain, ![X28, X29, X30, X31]:k3_enumset1(X28,X28,X29,X30,X31)=k2_enumset1(X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.43  fof(c_0_29, plain, ![X32, X33, X34]:(~r2_hidden(X32,k2_zfmisc_1(X33,X34))|k4_tarski(esk3_1(X32),esk4_1(X32))=X32), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.20/0.43  cnf(c_0_30, negated_conjecture, (r2_hidden(esk5_0,k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.43  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.43  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.43  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  fof(c_0_35, plain, ![X61, X62]:(k1_mcart_1(k4_tarski(X61,X62))=X61&k2_mcart_1(k4_tarski(X61,X62))=X62), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.20/0.43  cnf(c_0_36, plain, (k4_tarski(esk3_1(X1),esk4_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_37, negated_conjecture, (r2_hidden(esk5_0,k2_zfmisc_1(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.20/0.43  cnf(c_0_38, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.43  cnf(c_0_39, negated_conjecture, (k4_tarski(esk3_1(esk5_0),esk4_1(esk5_0))=esk5_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (esk3_1(esk5_0)=k1_mcart_1(esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.43  cnf(c_0_41, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.43  cnf(c_0_42, negated_conjecture, (k4_tarski(k1_mcart_1(esk5_0),esk4_1(esk5_0))=esk5_0), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.43  fof(c_0_43, plain, ![X50]:m1_subset_1(k2_subset_1(X50),k1_zfmisc_1(X50)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.43  fof(c_0_44, plain, ![X49]:k2_subset_1(X49)=X49, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.43  fof(c_0_45, plain, ![X39, X40, X41, X42]:(((r2_hidden(X39,X41)|~r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)))&(r2_hidden(X40,X42)|~r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42))))&(~r2_hidden(X39,X41)|~r2_hidden(X40,X42)|r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (esk4_1(esk5_0)=k2_mcart_1(esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.43  fof(c_0_47, plain, ![X54, X55]:(~m1_subset_1(X54,X55)|(v1_xboole_0(X55)|r2_hidden(X54,X55))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.43  cnf(c_0_48, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.43  cnf(c_0_49, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.43  fof(c_0_50, plain, ![X51]:~v1_xboole_0(k1_zfmisc_1(X51)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.43  fof(c_0_51, plain, ![X12, X13, X15, X16, X17]:(((r2_hidden(esk2_2(X12,X13),X12)|r1_xboole_0(X12,X13))&(r2_hidden(esk2_2(X12,X13),X13)|r1_xboole_0(X12,X13)))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|~r1_xboole_0(X15,X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.43  fof(c_0_52, plain, ![X44, X45, X46, X47]:((~r1_xboole_0(X44,X45)|r1_xboole_0(k2_zfmisc_1(X44,X46),k2_zfmisc_1(X45,X47)))&(~r1_xboole_0(X46,X47)|r1_xboole_0(k2_zfmisc_1(X44,X46),k2_zfmisc_1(X45,X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.20/0.43  cnf(c_0_53, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.43  cnf(c_0_54, negated_conjecture, (k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0))=esk5_0), inference(rw,[status(thm)],[c_0_42, c_0_46])).
% 0.20/0.43  cnf(c_0_55, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.43  cnf(c_0_56, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.43  cnf(c_0_57, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.43  fof(c_0_58, plain, ![X58, X59, X60]:((r2_hidden(k1_mcart_1(X58),X59)|~r2_hidden(X58,k2_zfmisc_1(X59,X60)))&(r2_hidden(k2_mcart_1(X58),X60)|~r2_hidden(X58,k2_zfmisc_1(X59,X60)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.20/0.43  cnf(c_0_59, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.43  cnf(c_0_60, plain, (r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, (r2_hidden(esk5_0,k2_zfmisc_1(X1,X2))|~r2_hidden(k2_mcart_1(esk5_0),X2)|~r2_hidden(k1_mcart_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.43  cnf(c_0_62, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.20/0.43  fof(c_0_63, plain, ![X37, X38]:((k4_xboole_0(k1_tarski(X37),X38)!=k1_tarski(X37)|~r2_hidden(X37,X38))&(r2_hidden(X37,X38)|k4_xboole_0(k1_tarski(X37),X38)=k1_tarski(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.20/0.43  fof(c_0_64, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.43  cnf(c_0_65, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.43  fof(c_0_66, plain, ![X48]:k3_tarski(k1_tarski(X48))=X48, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.20/0.43  cnf(c_0_67, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k2_zfmisc_1(X2,X4))|~r2_hidden(X3,k2_zfmisc_1(X1,X5))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.43  cnf(c_0_68, negated_conjecture, (r2_hidden(esk5_0,k2_zfmisc_1(X1,k1_zfmisc_1(k2_mcart_1(esk5_0))))|~r2_hidden(k1_mcart_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.43  fof(c_0_69, plain, ![X20, X21]:((~r1_xboole_0(X20,X21)|k4_xboole_0(X20,X21)=X20)&(k4_xboole_0(X20,X21)!=X20|r1_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.43  cnf(c_0_70, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.43  fof(c_0_71, plain, ![X56, X57]:((~m1_subset_1(X56,k1_zfmisc_1(X57))|r1_tarski(X56,X57))&(~r1_tarski(X56,X57)|m1_subset_1(X56,k1_zfmisc_1(X57)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.43  fof(c_0_72, plain, ![X52, X53]:(~r2_hidden(X52,X53)|m1_subset_1(X52,X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.43  cnf(c_0_73, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.43  cnf(c_0_74, negated_conjecture, (r2_hidden(k1_mcart_1(esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_65, c_0_37])).
% 0.20/0.43  fof(c_0_75, plain, ![X43]:r1_tarski(X43,k1_zfmisc_1(k3_tarski(X43))), inference(variable_rename,[status(thm)],[t100_zfmisc_1])).
% 0.20/0.43  cnf(c_0_76, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.43  cnf(c_0_77, negated_conjecture, (~r1_xboole_0(X1,X2)|~r2_hidden(esk5_0,k2_zfmisc_1(X1,X3))|~r2_hidden(k1_mcart_1(esk5_0),X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.43  cnf(c_0_78, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.43  cnf(c_0_79, plain, (k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)=k3_enumset1(X1,X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 0.20/0.43  cnf(c_0_80, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.43  cnf(c_0_81, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.43  cnf(c_0_82, negated_conjecture, (r2_hidden(k1_mcart_1(esk5_0),X1)|~r1_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.43  cnf(c_0_83, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.43  cnf(c_0_84, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.20/0.43  cnf(c_0_85, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.43  cnf(c_0_86, negated_conjecture, (~r1_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),X1)|~r2_hidden(k1_mcart_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_77, c_0_37])).
% 0.20/0.43  cnf(c_0_87, plain, (r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.43  fof(c_0_88, plain, ![X18, X19]:(((r1_tarski(X18,X19)|X18!=X19)&(r1_tarski(X19,X18)|X18!=X19))&(~r1_tarski(X18,X19)|~r1_tarski(X19,X18)|X18=X19)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.43  cnf(c_0_89, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.43  cnf(c_0_90, negated_conjecture, (r2_hidden(k1_mcart_1(esk5_0),k1_zfmisc_1(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 0.20/0.43  cnf(c_0_91, negated_conjecture, (k1_mcart_1(esk5_0)!=esk6_0|~r2_hidden(k2_mcart_1(esk5_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_92, negated_conjecture, (r2_hidden(k2_mcart_1(esk5_0),esk7_0)), inference(spm,[status(thm)],[c_0_85, c_0_37])).
% 0.20/0.43  cnf(c_0_93, negated_conjecture, (r2_hidden(esk6_0,X1)|~r2_hidden(k1_mcart_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.43  cnf(c_0_94, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.43  cnf(c_0_95, negated_conjecture, (r1_tarski(k1_mcart_1(esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.43  cnf(c_0_96, negated_conjecture, (k1_mcart_1(esk5_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92])])).
% 0.20/0.43  cnf(c_0_97, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(k1_mcart_1(esk5_0)))), inference(spm,[status(thm)],[c_0_93, c_0_62])).
% 0.20/0.43  cnf(c_0_98, negated_conjecture, (~r1_tarski(esk6_0,k1_mcart_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])).
% 0.20/0.43  cnf(c_0_99, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_97]), c_0_98]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 100
% 0.20/0.43  # Proof object clause steps            : 53
% 0.20/0.43  # Proof object formula steps           : 47
% 0.20/0.43  # Proof object conjectures             : 25
% 0.20/0.43  # Proof object clause conjectures      : 22
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 26
% 0.20/0.43  # Proof object initial formulas used   : 23
% 0.20/0.43  # Proof object generating inferences   : 20
% 0.20/0.43  # Proof object simplifying inferences  : 25
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 23
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 38
% 0.20/0.43  # Removed in clause preprocessing      : 5
% 0.20/0.43  # Initial clauses in saturation        : 33
% 0.20/0.43  # Processed clauses                    : 738
% 0.20/0.43  # ...of these trivial                  : 16
% 0.20/0.43  # ...subsumed                          : 219
% 0.20/0.43  # ...remaining for further processing  : 503
% 0.20/0.43  # Other redundant clauses eliminated   : 2
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 7
% 0.20/0.43  # Backward-rewritten                   : 3
% 0.20/0.43  # Generated clauses                    : 1757
% 0.20/0.43  # ...of the previous two non-trivial   : 1584
% 0.20/0.43  # Contextual simplify-reflections      : 0
% 0.20/0.43  # Paramodulations                      : 1755
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 2
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 459
% 0.20/0.43  #    Positive orientable unit clauses  : 111
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 31
% 0.20/0.43  #    Non-unit-clauses                  : 317
% 0.20/0.43  # Current number of unprocessed clauses: 873
% 0.20/0.43  # ...number of literals in the above   : 1924
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 47
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 15240
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 7699
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 194
% 0.20/0.43  # Unit Clause-clause subsumption calls : 1773
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 348
% 0.20/0.43  # BW rewrite match successes           : 3
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 28905
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.081 s
% 0.20/0.43  # System time              : 0.004 s
% 0.20/0.43  # Total time               : 0.085 s
% 0.20/0.43  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
