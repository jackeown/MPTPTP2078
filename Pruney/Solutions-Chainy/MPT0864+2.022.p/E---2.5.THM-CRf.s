%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:21 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 (1767 expanded)
%              Number of clauses        :   56 ( 872 expanded)
%              Number of leaves         :   15 ( 445 expanded)
%              Depth                    :   17
%              Number of atoms          :  232 (4451 expanded)
%              Number of equality atoms :  134 (2292 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t12_mcart_1,axiom,(
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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(c_0_15,plain,(
    ! [X45,X46] :
      ( ( ~ m1_subset_1(X45,k1_zfmisc_1(X46))
        | r1_tarski(X45,X46) )
      & ( ~ r1_tarski(X45,X46)
        | m1_subset_1(X45,k1_zfmisc_1(X46)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_16,plain,(
    ! [X43] : m1_subset_1(esk5_1(X43),X43) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_17,plain,(
    ! [X49,X50,X51] :
      ( ( k1_mcart_1(X49) = X50
        | ~ r2_hidden(X49,k2_zfmisc_1(k1_tarski(X50),X51)) )
      & ( r2_hidden(k2_mcart_1(X49),X51)
        | ~ r2_hidden(X49,k2_zfmisc_1(k1_tarski(X50),X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).

fof(c_0_18,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X39,X40] :
      ( ( k2_zfmisc_1(X39,X40) != k1_xboole_0
        | X39 = k1_xboole_0
        | X40 = k1_xboole_0 )
      & ( X39 != k1_xboole_0
        | k2_zfmisc_1(X39,X40) = k1_xboole_0 )
      & ( X40 != k1_xboole_0
        | k2_zfmisc_1(X39,X40) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_21,plain,(
    ! [X47,X48] :
      ( ~ r2_hidden(X47,X48)
      | ~ r1_tarski(X48,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r1_tarski(esk5_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_enumset1(X2,X2,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,esk5_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_34,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X30,X29)
        | X30 = X27
        | X30 = X28
        | X29 != k2_tarski(X27,X28) )
      & ( X31 != X27
        | r2_hidden(X31,X29)
        | X29 != k2_tarski(X27,X28) )
      & ( X31 != X28
        | r2_hidden(X31,X29)
        | X29 != k2_tarski(X27,X28) )
      & ( esk4_3(X32,X33,X34) != X32
        | ~ r2_hidden(esk4_3(X32,X33,X34),X34)
        | X34 = k2_tarski(X32,X33) )
      & ( esk4_3(X32,X33,X34) != X33
        | ~ r2_hidden(esk4_3(X32,X33,X34),X34)
        | X34 = k2_tarski(X32,X33) )
      & ( r2_hidden(esk4_3(X32,X33,X34),X34)
        | esk4_3(X32,X33,X34) = X32
        | esk4_3(X32,X33,X34) = X33
        | X34 = k2_tarski(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k1_mcart_1(X2))
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_36,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_26])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_44,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_45,plain,(
    ! [X41,X42] :
      ( ( k4_xboole_0(k1_tarski(X41),k1_tarski(X42)) != k1_tarski(X41)
        | X41 != X42 )
      & ( X41 = X42
        | k4_xboole_0(k1_tarski(X41),k1_tarski(X42)) = k1_tarski(X41) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_46,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_49,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X20
        | X21 != k1_tarski(X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_tarski(X20) )
      & ( ~ r2_hidden(esk3_2(X24,X25),X25)
        | esk3_2(X24,X25) != X24
        | X25 = k1_tarski(X24) )
      & ( r2_hidden(esk3_2(X24,X25),X25)
        | esk3_2(X24,X25) = X24
        | X25 = k1_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_51,plain,(
    ! [X52,X53] :
      ( k1_mcart_1(k4_tarski(X52,X53)) = X52
      & k2_mcart_1(k4_tarski(X52,X53)) = X53 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_52,negated_conjecture,
    ( esk7_0 = k4_tarski(esk8_0,esk9_0)
    & ( esk7_0 = k1_mcart_1(esk7_0)
      | esk7_0 = k2_mcart_1(esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_46])])])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( X1 != X2
    | k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)) != k1_enumset1(X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_56,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( esk7_0 = k4_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_59,plain,(
    ! [X54,X56,X57] :
      ( ( r2_hidden(esk6_1(X54),X54)
        | X54 = k1_xboole_0 )
      & ( ~ r2_hidden(X56,X54)
        | esk6_1(X54) != k4_tarski(X56,X57)
        | X54 = k1_xboole_0 )
      & ( ~ r2_hidden(X57,X54)
        | esk6_1(X54) != k4_tarski(X56,X57)
        | X54 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_60,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_53])).

cnf(c_0_61,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_25]),c_0_26])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) != k1_enumset1(X1,X1,X1) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_53]),c_0_47])).

cnf(c_0_64,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( esk7_0 = k1_mcart_1(esk7_0)
    | esk7_0 = k2_mcart_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,negated_conjecture,
    ( k1_mcart_1(esk7_0) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk6_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_60])).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( k1_enumset1(X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k2_mcart_1(esk7_0) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( k2_mcart_1(esk7_0) = esk7_0
    | esk8_0 = esk7_0 ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(X2,esk2_3(k1_xboole_0,X3,X1)) != esk6_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( esk2_3(k1_xboole_0,X1,k1_enumset1(X2,X2,X2)) = X2 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_68]),c_0_70])).

cnf(c_0_75,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_76,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk6_1(X2) != k4_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_77,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk9_0 = esk7_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( k4_tarski(X1,X2) != esk6_1(k1_enumset1(X2,X2,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_70])).

cnf(c_0_79,plain,
    ( esk6_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_75]),c_0_70])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(esk2_3(k1_xboole_0,X2,X1),X3) != esk6_1(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( k4_tarski(esk8_0,esk7_0) = esk7_0
    | esk8_0 = esk7_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_77])).

cnf(c_0_82,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,plain,
    ( k4_tarski(X1,X2) != esk6_1(k1_enumset1(X1,X1,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_74]),c_0_70])).

cnf(c_0_84,negated_conjecture,
    ( esk8_0 = esk7_0 ),
    inference(sr,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,plain,
    ( k4_tarski(X1,X2) != X1 ),
    inference(rw,[status(thm)],[c_0_83,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_84]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:42:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.029 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.38  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.20/0.38  fof(t12_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.38  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.20/0.38  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.20/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.38  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.20/0.38  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.20/0.38  fof(c_0_15, plain, ![X45, X46]:((~m1_subset_1(X45,k1_zfmisc_1(X46))|r1_tarski(X45,X46))&(~r1_tarski(X45,X46)|m1_subset_1(X45,k1_zfmisc_1(X46)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.38  fof(c_0_16, plain, ![X43]:m1_subset_1(esk5_1(X43),X43), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.20/0.38  fof(c_0_17, plain, ![X49, X50, X51]:((k1_mcart_1(X49)=X50|~r2_hidden(X49,k2_zfmisc_1(k1_tarski(X50),X51)))&(r2_hidden(k2_mcart_1(X49),X51)|~r2_hidden(X49,k2_zfmisc_1(k1_tarski(X50),X51)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).
% 0.20/0.38  fof(c_0_18, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_19, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_20, plain, ![X39, X40]:((k2_zfmisc_1(X39,X40)!=k1_xboole_0|(X39=k1_xboole_0|X40=k1_xboole_0))&((X39!=k1_xboole_0|k2_zfmisc_1(X39,X40)=k1_xboole_0)&(X40!=k1_xboole_0|k2_zfmisc_1(X39,X40)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_21, plain, ![X47, X48]:(~r2_hidden(X47,X48)|~r1_tarski(X48,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.38  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_23, plain, (m1_subset_1(esk5_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_24, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_27, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_29, plain, (r1_tarski(esk5_1(k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.38  cnf(c_0_30, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k1_enumset1(X2,X2,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.20/0.38  cnf(c_0_31, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_32, plain, (~r2_hidden(X1,esk5_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.38  cnf(c_0_33, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.38  fof(c_0_34, plain, ![X27, X28, X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X30,X29)|(X30=X27|X30=X28)|X29!=k2_tarski(X27,X28))&((X31!=X27|r2_hidden(X31,X29)|X29!=k2_tarski(X27,X28))&(X31!=X28|r2_hidden(X31,X29)|X29!=k2_tarski(X27,X28))))&(((esk4_3(X32,X33,X34)!=X32|~r2_hidden(esk4_3(X32,X33,X34),X34)|X34=k2_tarski(X32,X33))&(esk4_3(X32,X33,X34)!=X33|~r2_hidden(esk4_3(X32,X33,X34),X34)|X34=k2_tarski(X32,X33)))&(r2_hidden(esk4_3(X32,X33,X34),X34)|(esk4_3(X32,X33,X34)=X32|esk4_3(X32,X33,X34)=X33)|X34=k2_tarski(X32,X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_35, plain, (~r2_hidden(X1,k1_mcart_1(X2))|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.38  fof(c_0_36, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_37, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_38, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_35, c_0_33])).
% 0.20/0.38  cnf(c_0_39, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_37, c_0_26])).
% 0.20/0.38  cnf(c_0_41, plain, (r1_tarski(k1_xboole_0,X1)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.38  cnf(c_0_42, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).
% 0.20/0.38  cnf(c_0_43, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.38  fof(c_0_44, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.38  fof(c_0_45, plain, ![X41, X42]:((k4_xboole_0(k1_tarski(X41),k1_tarski(X42))!=k1_tarski(X41)|X41!=X42)&(X41=X42|k4_xboole_0(k1_tarski(X41),k1_tarski(X42))=k1_tarski(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.20/0.38  fof(c_0_46, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.20/0.38  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_43])).
% 0.20/0.38  cnf(c_0_48, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.38  fof(c_0_49, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X22,X21)|X22=X20|X21!=k1_tarski(X20))&(X23!=X20|r2_hidden(X23,X21)|X21!=k1_tarski(X20)))&((~r2_hidden(esk3_2(X24,X25),X25)|esk3_2(X24,X25)!=X24|X25=k1_tarski(X24))&(r2_hidden(esk3_2(X24,X25),X25)|esk3_2(X24,X25)=X24|X25=k1_tarski(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_50, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.38  fof(c_0_51, plain, ![X52, X53]:(k1_mcart_1(k4_tarski(X52,X53))=X52&k2_mcart_1(k4_tarski(X52,X53))=X53), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.20/0.38  fof(c_0_52, negated_conjecture, (esk7_0=k4_tarski(esk8_0,esk9_0)&(esk7_0=k1_mcart_1(esk7_0)|esk7_0=k2_mcart_1(esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_46])])])).
% 0.20/0.38  cnf(c_0_53, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.38  cnf(c_0_54, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.38  cnf(c_0_55, plain, (X1!=X2|k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2))!=k1_enumset1(X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26])).
% 0.20/0.38  cnf(c_0_56, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.38  cnf(c_0_57, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (esk7_0=k4_tarski(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.38  fof(c_0_59, plain, ![X54, X56, X57]:((r2_hidden(esk6_1(X54),X54)|X54=k1_xboole_0)&((~r2_hidden(X56,X54)|esk6_1(X54)!=k4_tarski(X56,X57)|X54=k1_xboole_0)&(~r2_hidden(X57,X54)|esk6_1(X54)!=k4_tarski(X56,X57)|X54=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.20/0.38  cnf(c_0_60, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_53])).
% 0.20/0.38  cnf(c_0_61, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_25]), c_0_26])).
% 0.20/0.38  cnf(c_0_62, plain, (k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))!=k1_enumset1(X1,X1,X1)), inference(er,[status(thm)],[c_0_55])).
% 0.20/0.38  cnf(c_0_63, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_53]), c_0_47])).
% 0.20/0.38  cnf(c_0_64, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (esk7_0=k1_mcart_1(esk7_0)|esk7_0=k2_mcart_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (k1_mcart_1(esk7_0)=esk8_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.38  cnf(c_0_67, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk6_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.38  cnf(c_0_68, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_60])).
% 0.20/0.38  cnf(c_0_69, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_61])).
% 0.20/0.38  cnf(c_0_70, plain, (k1_enumset1(X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, (k2_mcart_1(esk7_0)=esk9_0), inference(spm,[status(thm)],[c_0_64, c_0_58])).
% 0.20/0.38  cnf(c_0_72, negated_conjecture, (k2_mcart_1(esk7_0)=esk7_0|esk8_0=esk7_0), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.38  cnf(c_0_73, plain, (X1=k1_xboole_0|k4_tarski(X2,esk2_3(k1_xboole_0,X3,X1))!=esk6_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.38  cnf(c_0_74, plain, (esk2_3(k1_xboole_0,X1,k1_enumset1(X2,X2,X2))=X2), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_68]), c_0_70])).
% 0.20/0.38  cnf(c_0_75, plain, (r2_hidden(esk6_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.38  cnf(c_0_76, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk6_1(X2)!=k4_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, (esk8_0=esk7_0|esk9_0=esk7_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.38  cnf(c_0_78, plain, (k4_tarski(X1,X2)!=esk6_1(k1_enumset1(X2,X2,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_70])).
% 0.20/0.38  cnf(c_0_79, plain, (esk6_1(k1_enumset1(X1,X1,X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_75]), c_0_70])).
% 0.20/0.38  cnf(c_0_80, plain, (X1=k1_xboole_0|k4_tarski(esk2_3(k1_xboole_0,X2,X1),X3)!=esk6_1(X1)), inference(spm,[status(thm)],[c_0_76, c_0_68])).
% 0.20/0.38  cnf(c_0_81, negated_conjecture, (k4_tarski(esk8_0,esk7_0)=esk7_0|esk8_0=esk7_0), inference(spm,[status(thm)],[c_0_58, c_0_77])).
% 0.20/0.38  cnf(c_0_82, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.38  cnf(c_0_83, plain, (k4_tarski(X1,X2)!=esk6_1(k1_enumset1(X1,X1,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_74]), c_0_70])).
% 0.20/0.38  cnf(c_0_84, negated_conjecture, (esk8_0=esk7_0), inference(sr,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.38  cnf(c_0_85, plain, (k4_tarski(X1,X2)!=X1), inference(rw,[status(thm)],[c_0_83, c_0_79])).
% 0.20/0.38  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_84]), c_0_85]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 87
% 0.20/0.38  # Proof object clause steps            : 56
% 0.20/0.38  # Proof object formula steps           : 31
% 0.20/0.38  # Proof object conjectures             : 12
% 0.20/0.38  # Proof object clause conjectures      : 9
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 20
% 0.20/0.38  # Proof object initial formulas used   : 15
% 0.20/0.38  # Proof object generating inferences   : 22
% 0.20/0.38  # Proof object simplifying inferences  : 29
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 15
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 39
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 37
% 0.20/0.38  # Processed clauses                    : 177
% 0.20/0.38  # ...of these trivial                  : 2
% 0.20/0.38  # ...subsumed                          : 52
% 0.20/0.38  # ...remaining for further processing  : 123
% 0.20/0.38  # Other redundant clauses eliminated   : 35
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 9
% 0.20/0.38  # Generated clauses                    : 499
% 0.20/0.38  # ...of the previous two non-trivial   : 455
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 447
% 0.20/0.38  # Factorizations                       : 18
% 0.20/0.38  # Equation resolutions                 : 35
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 63
% 0.20/0.38  #    Positive orientable unit clauses  : 18
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 7
% 0.20/0.38  #    Non-unit-clauses                  : 38
% 0.20/0.38  # Current number of unprocessed clauses: 337
% 0.20/0.38  # ...number of literals in the above   : 1261
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 51
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 284
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 222
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.20/0.38  # Unit Clause-clause subsumption calls : 148
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 21
% 0.20/0.38  # BW rewrite match successes           : 7
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 6868
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.040 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.044 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
