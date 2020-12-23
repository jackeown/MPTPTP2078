%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:53 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 337 expanded)
%              Number of clauses        :   49 ( 140 expanded)
%              Number of leaves         :   14 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  244 (1326 expanded)
%              Number of equality atoms :  180 (1050 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                & X4 != k6_mcart_1(X1,X2,X3,X4)
                & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t50_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                  & X4 != k6_mcart_1(X1,X2,X3,X4)
                  & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_mcart_1])).

fof(c_0_15,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r2_hidden(X39,X41)
        | k4_xboole_0(k2_tarski(X39,X40),X41) != k2_tarski(X39,X40) )
      & ( ~ r2_hidden(X40,X41)
        | k4_xboole_0(k2_tarski(X39,X40),X41) != k2_tarski(X39,X40) )
      & ( r2_hidden(X39,X41)
        | r2_hidden(X40,X41)
        | k4_xboole_0(k2_tarski(X39,X40),X41) = k2_tarski(X39,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

fof(c_0_16,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X60,X61,X62,X63] :
      ( ( k5_mcart_1(X60,X61,X62,X63) = k1_mcart_1(k1_mcart_1(X63))
        | ~ m1_subset_1(X63,k3_zfmisc_1(X60,X61,X62))
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0
        | X62 = k1_xboole_0 )
      & ( k6_mcart_1(X60,X61,X62,X63) = k2_mcart_1(k1_mcart_1(X63))
        | ~ m1_subset_1(X63,k3_zfmisc_1(X60,X61,X62))
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0
        | X62 = k1_xboole_0 )
      & ( k7_mcart_1(X60,X61,X62,X63) = k2_mcart_1(X63)
        | ~ m1_subset_1(X63,k3_zfmisc_1(X60,X61,X62))
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0
        | X62 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_18,plain,(
    ! [X45,X46,X47] : k3_zfmisc_1(X45,X46,X47) = k2_zfmisc_1(k2_zfmisc_1(X45,X46),X47) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_19,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & esk7_0 != k1_xboole_0
    & m1_subset_1(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))
    & ( esk8_0 = k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)
      | esk8_0 = k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)
      | esk8_0 = k7_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_23,plain,(
    ! [X56,X57,X58,X59] :
      ( X56 = k1_xboole_0
      | X57 = k1_xboole_0
      | X58 = k1_xboole_0
      | ~ m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))
      | X59 = k3_mcart_1(k5_mcart_1(X56,X57,X58,X59),k6_mcart_1(X56,X57,X58,X59),k7_mcart_1(X56,X57,X58,X59)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_24,plain,(
    ! [X42,X43,X44] : k3_mcart_1(X42,X43,X44) = k4_tarski(k4_tarski(X42,X43),X44) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_25,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X31,X30)
        | X31 = X29
        | X30 != k1_tarski(X29) )
      & ( X32 != X29
        | r2_hidden(X32,X30)
        | X30 != k1_tarski(X29) )
      & ( ~ r2_hidden(esk3_2(X33,X34),X34)
        | esk3_2(X33,X34) != X33
        | X34 = k1_tarski(X33) )
      & ( r2_hidden(esk3_2(X33,X34),X34)
        | esk3_2(X33,X34) = X33
        | X34 = k1_tarski(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_29,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k1_enumset1(X3,X3,X1),X2) != k1_enumset1(X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X51,X53,X54,X55] :
      ( ( r2_hidden(esk4_1(X51),X51)
        | X51 = k1_xboole_0 )
      & ( ~ r2_hidden(X53,X51)
        | esk4_1(X51) != k3_mcart_1(X53,X54,X55)
        | X51 = k1_xboole_0 )
      & ( ~ r2_hidden(X54,X51)
        | esk4_1(X51) != k3_mcart_1(X53,X54,X55)
        | X51 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

fof(c_0_33,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X18
        | X22 = X19
        | X22 = X20
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( X23 != X18
        | r2_hidden(X23,X21)
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( X23 != X19
        | r2_hidden(X23,X21)
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( esk2_4(X24,X25,X26,X27) != X24
        | ~ r2_hidden(esk2_4(X24,X25,X26,X27),X27)
        | X27 = k1_enumset1(X24,X25,X26) )
      & ( esk2_4(X24,X25,X26,X27) != X25
        | ~ r2_hidden(esk2_4(X24,X25,X26,X27),X27)
        | X27 = k1_enumset1(X24,X25,X26) )
      & ( esk2_4(X24,X25,X26,X27) != X26
        | ~ r2_hidden(esk2_4(X24,X25,X26,X27),X27)
        | X27 = k1_enumset1(X24,X25,X26) )
      & ( r2_hidden(esk2_4(X24,X25,X26,X27),X27)
        | esk2_4(X24,X25,X26,X27) = X24
        | esk2_4(X24,X25,X26,X27) = X25
        | esk2_4(X24,X25,X26,X27) = X26
        | X27 = k1_enumset1(X24,X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_34,plain,(
    ! [X48,X49,X50] :
      ( ( X48 != k1_mcart_1(X48)
        | X48 != k4_tarski(X49,X50) )
      & ( X48 != k2_mcart_1(X48)
        | X48 != k4_tarski(X49,X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_45,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_48,plain,(
    ! [X64,X65] :
      ( k1_mcart_1(k4_tarski(X64,X65)) = X64
      & k2_mcart_1(k4_tarski(X64,X65)) = X65 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_49,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk4_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_50,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_26])).

cnf(c_0_51,negated_conjecture,
    ( k7_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = k2_mcart_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_52,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_21])).

cnf(c_0_53,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_55,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk4_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_58,plain,
    ( X2 = k1_xboole_0
    | esk4_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)),k2_mcart_1(esk8_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_38]),c_0_51]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( r2_hidden(esk4_1(k1_enumset1(X1,X2,X3)),k1_enumset1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( esk8_0 = k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)
    | esk8_0 = k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)
    | esk8_0 = k7_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_63,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( X2 = k1_xboole_0
    | esk4_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_36])).

cnf(c_0_65,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk4_1(X1) != esk8_0
    | ~ r2_hidden(k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
    ( esk4_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k2_mcart_1(esk8_0) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( k2_mcart_1(esk8_0) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_59])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk4_1(X1) != esk8_0
    | ~ r2_hidden(k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | ~ r2_hidden(k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk8_0,esk8_0,esk8_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_72,negated_conjecture,
    ( k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0 ),
    inference(sr,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_69])])).

cnf(c_0_74,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | ~ r2_hidden(k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk8_0,esk8_0,esk8_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_66])])).

cnf(c_0_75,negated_conjecture,
    ( k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) = esk8_0
    | k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_76,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_73])])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_76]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:05:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.42  # and selection function SelectNegativeLiterals.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.029 s
% 0.21/0.42  # Presaturation interreduction done
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.21/0.42  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.21/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.42  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.21/0.42  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.21/0.42  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.21/0.42  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.21/0.42  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.21/0.42  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.42  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.21/0.42  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.21/0.42  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.21/0.42  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.21/0.42  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.21/0.42  fof(c_0_15, plain, ![X39, X40, X41]:(((~r2_hidden(X39,X41)|k4_xboole_0(k2_tarski(X39,X40),X41)!=k2_tarski(X39,X40))&(~r2_hidden(X40,X41)|k4_xboole_0(k2_tarski(X39,X40),X41)!=k2_tarski(X39,X40)))&(r2_hidden(X39,X41)|r2_hidden(X40,X41)|k4_xboole_0(k2_tarski(X39,X40),X41)=k2_tarski(X39,X40))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 0.21/0.42  fof(c_0_16, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.42  fof(c_0_17, plain, ![X60, X61, X62, X63]:(((k5_mcart_1(X60,X61,X62,X63)=k1_mcart_1(k1_mcart_1(X63))|~m1_subset_1(X63,k3_zfmisc_1(X60,X61,X62))|(X60=k1_xboole_0|X61=k1_xboole_0|X62=k1_xboole_0))&(k6_mcart_1(X60,X61,X62,X63)=k2_mcart_1(k1_mcart_1(X63))|~m1_subset_1(X63,k3_zfmisc_1(X60,X61,X62))|(X60=k1_xboole_0|X61=k1_xboole_0|X62=k1_xboole_0)))&(k7_mcart_1(X60,X61,X62,X63)=k2_mcart_1(X63)|~m1_subset_1(X63,k3_zfmisc_1(X60,X61,X62))|(X60=k1_xboole_0|X61=k1_xboole_0|X62=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.21/0.42  fof(c_0_18, plain, ![X45, X46, X47]:k3_zfmisc_1(X45,X46,X47)=k2_zfmisc_1(k2_zfmisc_1(X45,X46),X47), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.21/0.42  fof(c_0_19, negated_conjecture, (((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&(m1_subset_1(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))&(esk8_0=k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k7_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.21/0.42  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.42  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.42  fof(c_0_22, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.21/0.42  fof(c_0_23, plain, ![X56, X57, X58, X59]:(X56=k1_xboole_0|X57=k1_xboole_0|X58=k1_xboole_0|(~m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))|X59=k3_mcart_1(k5_mcart_1(X56,X57,X58,X59),k6_mcart_1(X56,X57,X58,X59),k7_mcart_1(X56,X57,X58,X59)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.21/0.42  fof(c_0_24, plain, ![X42, X43, X44]:k3_mcart_1(X42,X43,X44)=k4_tarski(k4_tarski(X42,X43),X44), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.21/0.42  cnf(c_0_25, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.42  cnf(c_0_26, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.42  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  fof(c_0_28, plain, ![X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X31,X30)|X31=X29|X30!=k1_tarski(X29))&(X32!=X29|r2_hidden(X32,X30)|X30!=k1_tarski(X29)))&((~r2_hidden(esk3_2(X33,X34),X34)|esk3_2(X33,X34)!=X33|X34=k1_tarski(X33))&(r2_hidden(esk3_2(X33,X34),X34)|esk3_2(X33,X34)=X33|X34=k1_tarski(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.42  fof(c_0_29, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.42  cnf(c_0_30, plain, (k4_xboole_0(k1_enumset1(X3,X3,X1),X2)!=k1_enumset1(X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21])).
% 0.21/0.42  cnf(c_0_31, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.42  fof(c_0_32, plain, ![X51, X53, X54, X55]:((r2_hidden(esk4_1(X51),X51)|X51=k1_xboole_0)&((~r2_hidden(X53,X51)|esk4_1(X51)!=k3_mcart_1(X53,X54,X55)|X51=k1_xboole_0)&(~r2_hidden(X54,X51)|esk4_1(X51)!=k3_mcart_1(X53,X54,X55)|X51=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.21/0.42  fof(c_0_33, plain, ![X18, X19, X20, X21, X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X22,X21)|(X22=X18|X22=X19|X22=X20)|X21!=k1_enumset1(X18,X19,X20))&(((X23!=X18|r2_hidden(X23,X21)|X21!=k1_enumset1(X18,X19,X20))&(X23!=X19|r2_hidden(X23,X21)|X21!=k1_enumset1(X18,X19,X20)))&(X23!=X20|r2_hidden(X23,X21)|X21!=k1_enumset1(X18,X19,X20))))&((((esk2_4(X24,X25,X26,X27)!=X24|~r2_hidden(esk2_4(X24,X25,X26,X27),X27)|X27=k1_enumset1(X24,X25,X26))&(esk2_4(X24,X25,X26,X27)!=X25|~r2_hidden(esk2_4(X24,X25,X26,X27),X27)|X27=k1_enumset1(X24,X25,X26)))&(esk2_4(X24,X25,X26,X27)!=X26|~r2_hidden(esk2_4(X24,X25,X26,X27),X27)|X27=k1_enumset1(X24,X25,X26)))&(r2_hidden(esk2_4(X24,X25,X26,X27),X27)|(esk2_4(X24,X25,X26,X27)=X24|esk2_4(X24,X25,X26,X27)=X25|esk2_4(X24,X25,X26,X27)=X26)|X27=k1_enumset1(X24,X25,X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.21/0.42  fof(c_0_34, plain, ![X48, X49, X50]:((X48!=k1_mcart_1(X48)|X48!=k4_tarski(X49,X50))&(X48!=k2_mcart_1(X48)|X48!=k4_tarski(X49,X50))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.21/0.42  cnf(c_0_35, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.42  cnf(c_0_36, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.42  cnf(c_0_37, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.42  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 0.21/0.42  cnf(c_0_39, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  cnf(c_0_40, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  cnf(c_0_41, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  cnf(c_0_42, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.42  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.42  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.42  cnf(c_0_45, plain, (r2_hidden(esk4_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.42  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.42  cnf(c_0_47, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.42  fof(c_0_48, plain, ![X64, X65]:(k1_mcart_1(k4_tarski(X64,X65))=X64&k2_mcart_1(k4_tarski(X64,X65))=X65), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.21/0.42  cnf(c_0_49, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk4_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.42  cnf(c_0_50, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_26])).
% 0.21/0.42  cnf(c_0_51, negated_conjecture, (k7_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=k2_mcart_1(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.21/0.42  cnf(c_0_52, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_21])).
% 0.21/0.42  cnf(c_0_53, plain, (r2_hidden(esk4_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.42  cnf(c_0_54, plain, (r2_hidden(X1,k1_enumset1(X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 0.21/0.42  cnf(c_0_55, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_47])).
% 0.21/0.42  cnf(c_0_56, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.42  cnf(c_0_57, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk4_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.42  cnf(c_0_58, plain, (X2=k1_xboole_0|esk4_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_49, c_0_36])).
% 0.21/0.42  cnf(c_0_59, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)),k2_mcart_1(esk8_0))=esk8_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_38]), c_0_51]), c_0_39]), c_0_40]), c_0_41])).
% 0.21/0.42  cnf(c_0_60, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_52])).
% 0.21/0.42  cnf(c_0_61, plain, (r2_hidden(esk4_1(k1_enumset1(X1,X2,X3)),k1_enumset1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.42  cnf(c_0_62, negated_conjecture, (esk8_0=k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)|esk8_0=k7_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  cnf(c_0_63, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.21/0.42  cnf(c_0_64, plain, (X2=k1_xboole_0|esk4_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_36])).
% 0.21/0.42  cnf(c_0_65, negated_conjecture, (X1=k1_xboole_0|esk4_1(X1)!=esk8_0|~r2_hidden(k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.42  cnf(c_0_66, plain, (esk4_1(k1_enumset1(X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.42  cnf(c_0_67, negated_conjecture, (k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k2_mcart_1(esk8_0)=esk8_0), inference(spm,[status(thm)],[c_0_62, c_0_51])).
% 0.21/0.42  cnf(c_0_68, negated_conjecture, (k2_mcart_1(esk8_0)!=esk8_0), inference(spm,[status(thm)],[c_0_63, c_0_59])).
% 0.21/0.42  cnf(c_0_69, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.42  cnf(c_0_70, negated_conjecture, (X1=k1_xboole_0|esk4_1(X1)!=esk8_0|~r2_hidden(k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),X1)), inference(spm,[status(thm)],[c_0_64, c_0_59])).
% 0.21/0.42  cnf(c_0_71, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_xboole_0|~r2_hidden(k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk8_0,esk8_0,esk8_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66])])).
% 0.21/0.42  cnf(c_0_72, negated_conjecture, (k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k6_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0), inference(sr,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.42  cnf(c_0_73, plain, (r2_hidden(X1,k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_69])])).
% 0.21/0.42  cnf(c_0_74, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_xboole_0|~r2_hidden(k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk8_0,esk8_0,esk8_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_66])])).
% 0.21/0.42  cnf(c_0_75, negated_conjecture, (k5_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)=esk8_0|k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 0.21/0.42  cnf(c_0_76, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_73])])).
% 0.21/0.42  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_76]), c_0_44]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 78
% 0.21/0.42  # Proof object clause steps            : 49
% 0.21/0.42  # Proof object formula steps           : 29
% 0.21/0.42  # Proof object conjectures             : 21
% 0.21/0.42  # Proof object clause conjectures      : 18
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 21
% 0.21/0.42  # Proof object initial formulas used   : 14
% 0.21/0.42  # Proof object generating inferences   : 15
% 0.21/0.42  # Proof object simplifying inferences  : 32
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 16
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 43
% 0.21/0.42  # Removed in clause preprocessing      : 5
% 0.21/0.42  # Initial clauses in saturation        : 38
% 0.21/0.42  # Processed clauses                    : 366
% 0.21/0.42  # ...of these trivial                  : 11
% 0.21/0.42  # ...subsumed                          : 159
% 0.21/0.42  # ...remaining for further processing  : 196
% 0.21/0.42  # Other redundant clauses eliminated   : 201
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 7
% 0.21/0.42  # Backward-rewritten                   : 12
% 0.21/0.42  # Generated clauses                    : 3276
% 0.21/0.42  # ...of the previous two non-trivial   : 2326
% 0.21/0.42  # Contextual simplify-reflections      : 0
% 0.21/0.42  # Paramodulations                      : 3072
% 0.21/0.42  # Factorizations                       : 6
% 0.21/0.42  # Equation resolutions                 : 201
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 128
% 0.21/0.42  #    Positive orientable unit clauses  : 28
% 0.21/0.42  #    Positive unorientable unit clauses: 0
% 0.21/0.42  #    Negative unit clauses             : 11
% 0.21/0.42  #    Non-unit-clauses                  : 89
% 0.21/0.42  # Current number of unprocessed clauses: 1995
% 0.21/0.42  # ...number of literals in the above   : 6577
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 62
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 1047
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 675
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 141
% 0.21/0.42  # Unit Clause-clause subsumption calls : 222
% 0.21/0.42  # Rewrite failures with RHS unbound    : 0
% 0.21/0.42  # BW rewrite match attempts            : 24
% 0.21/0.42  # BW rewrite match successes           : 8
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 43807
% 0.21/0.42  
% 0.21/0.42  # -------------------------------------------------
% 0.21/0.42  # User time                : 0.071 s
% 0.21/0.42  # System time              : 0.005 s
% 0.21/0.42  # Total time               : 0.076 s
% 0.21/0.42  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
