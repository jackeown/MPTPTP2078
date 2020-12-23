%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:53 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 124 expanded)
%              Number of clauses        :   42 (  52 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  246 ( 652 expanded)
%              Number of equality atoms :   57 ( 105 expanded)
%              Maximal formula depth    :   32 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( m1_subset_1(X3,X1)
         => ! [X4] :
              ( m1_subset_1(X4,X1)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ! [X6] :
                      ( m1_subset_1(X6,X1)
                     => ! [X7] :
                          ( m1_subset_1(X7,X1)
                         => ( X1 != k1_xboole_0
                           => m1_subset_1(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_subset_1)).

fof(t59_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( m1_subset_1(X3,X1)
         => ! [X4] :
              ( m1_subset_1(X4,X1)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ! [X6] :
                      ( m1_subset_1(X6,X1)
                     => ( X1 != k1_xboole_0
                       => m1_subset_1(k3_enumset1(X2,X3,X4,X5,X6),k1_zfmisc_1(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,X1)
       => ! [X3] :
            ( m1_subset_1(X3,X1)
           => ! [X4] :
                ( m1_subset_1(X4,X1)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X1)
                       => ! [X7] :
                            ( m1_subset_1(X7,X1)
                           => ( X1 != k1_xboole_0
                             => m1_subset_1(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X1)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t60_subset_1])).

fof(c_0_12,plain,(
    ! [X57,X58,X59,X60,X61,X62] :
      ( ~ m1_subset_1(X58,X57)
      | ~ m1_subset_1(X59,X57)
      | ~ m1_subset_1(X60,X57)
      | ~ m1_subset_1(X61,X57)
      | ~ m1_subset_1(X62,X57)
      | X57 = k1_xboole_0
      | m1_subset_1(k3_enumset1(X58,X59,X60,X61,X62),k1_zfmisc_1(X57)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_subset_1])])])).

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,esk4_0)
    & m1_subset_1(esk6_0,esk4_0)
    & m1_subset_1(esk7_0,esk4_0)
    & m1_subset_1(esk8_0,esk4_0)
    & m1_subset_1(esk9_0,esk4_0)
    & m1_subset_1(esk10_0,esk4_0)
    & esk4_0 != k1_xboole_0
    & ~ m1_subset_1(k4_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),k1_zfmisc_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X54,X55,X56] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(X54))
      | ~ r2_hidden(X56,X55)
      | r2_hidden(X56,X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_15,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k3_enumset1(X1,X3,X4,X5,X6),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,X2)
    | ~ m1_subset_1(X4,X2)
    | ~ m1_subset_1(X5,X2)
    | ~ m1_subset_1(X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk10_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51] :
      ( ( ~ r2_hidden(X44,X43)
        | X44 = X38
        | X44 = X39
        | X44 = X40
        | X44 = X41
        | X44 = X42
        | X43 != k3_enumset1(X38,X39,X40,X41,X42) )
      & ( X45 != X38
        | r2_hidden(X45,X43)
        | X43 != k3_enumset1(X38,X39,X40,X41,X42) )
      & ( X45 != X39
        | r2_hidden(X45,X43)
        | X43 != k3_enumset1(X38,X39,X40,X41,X42) )
      & ( X45 != X40
        | r2_hidden(X45,X43)
        | X43 != k3_enumset1(X38,X39,X40,X41,X42) )
      & ( X45 != X41
        | r2_hidden(X45,X43)
        | X43 != k3_enumset1(X38,X39,X40,X41,X42) )
      & ( X45 != X42
        | r2_hidden(X45,X43)
        | X43 != k3_enumset1(X38,X39,X40,X41,X42) )
      & ( esk3_6(X46,X47,X48,X49,X50,X51) != X46
        | ~ r2_hidden(esk3_6(X46,X47,X48,X49,X50,X51),X51)
        | X51 = k3_enumset1(X46,X47,X48,X49,X50) )
      & ( esk3_6(X46,X47,X48,X49,X50,X51) != X47
        | ~ r2_hidden(esk3_6(X46,X47,X48,X49,X50,X51),X51)
        | X51 = k3_enumset1(X46,X47,X48,X49,X50) )
      & ( esk3_6(X46,X47,X48,X49,X50,X51) != X48
        | ~ r2_hidden(esk3_6(X46,X47,X48,X49,X50,X51),X51)
        | X51 = k3_enumset1(X46,X47,X48,X49,X50) )
      & ( esk3_6(X46,X47,X48,X49,X50,X51) != X49
        | ~ r2_hidden(esk3_6(X46,X47,X48,X49,X50,X51),X51)
        | X51 = k3_enumset1(X46,X47,X48,X49,X50) )
      & ( esk3_6(X46,X47,X48,X49,X50,X51) != X50
        | ~ r2_hidden(esk3_6(X46,X47,X48,X49,X50,X51),X51)
        | X51 = k3_enumset1(X46,X47,X48,X49,X50) )
      & ( r2_hidden(esk3_6(X46,X47,X48,X49,X50,X51),X51)
        | esk3_6(X46,X47,X48,X49,X50,X51) = X46
        | esk3_6(X46,X47,X48,X49,X50,X51) = X47
        | esk3_6(X46,X47,X48,X49,X50,X51) = X48
        | esk3_6(X46,X47,X48,X49,X50,X51) = X49
        | esk3_6(X46,X47,X48,X49,X50,X51) = X50
        | X51 = k3_enumset1(X46,X47,X48,X49,X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,esk10_0),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X2,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X5,esk4_0)
    | ~ r2_hidden(X1,k3_enumset1(X5,X4,X3,X2,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X1,X3,X4,X5)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).

fof(c_0_24,plain,(
    ! [X15,X16,X17,X18,X19,X20] : k4_enumset1(X15,X16,X17,X18,X19,X20) = k2_xboole_0(k1_tarski(X15),k3_enumset1(X16,X17,X18,X19,X20)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

fof(c_0_25,plain,(
    ! [X36,X37] :
      ( ( ~ m1_subset_1(X37,X36)
        | r2_hidden(X37,X36)
        | v1_xboole_0(X36) )
      & ( ~ r2_hidden(X37,X36)
        | m1_subset_1(X37,X36)
        | v1_xboole_0(X36) )
      & ( ~ m1_subset_1(X37,X36)
        | v1_xboole_0(X37)
        | ~ v1_xboole_0(X36) )
      & ( ~ v1_xboole_0(X37)
        | m1_subset_1(X37,X36)
        | ~ v1_xboole_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_26,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X4,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(k4_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X29,X28)
        | r1_tarski(X29,X27)
        | X28 != k1_zfmisc_1(X27) )
      & ( ~ r1_tarski(X30,X27)
        | r2_hidden(X30,X28)
        | X28 != k1_zfmisc_1(X27) )
      & ( ~ r2_hidden(esk2_2(X31,X32),X32)
        | ~ r1_tarski(esk2_2(X31,X32),X31)
        | X32 = k1_zfmisc_1(X31) )
      & ( r2_hidden(esk2_2(X31,X32),X32)
        | r1_tarski(esk2_2(X31,X32),X31)
        | X32 = k1_zfmisc_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X3,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(k1_tarski(esk5_0),k3_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)),k1_zfmisc_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_37,plain,(
    ! [X53] : ~ v1_xboole_0(k1_zfmisc_1(X53)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(esk5_0),k3_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_36])).

fof(c_0_41,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X14,X13)
      | r1_tarski(k2_xboole_0(X12,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk10_0,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(esk5_0),k3_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k3_enumset1(X1,X2,X3,X4,esk10_0),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_20]),c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk10_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(k3_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),esk4_0)
    | ~ r1_tarski(k1_tarski(esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k3_enumset1(X1,X2,X3,X4,esk10_0),esk4_0)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk9_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk8_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_58,plain,(
    ! [X34,X35] :
      ( ( ~ r1_tarski(k1_tarski(X34),X35)
        | r2_hidden(X34,X35) )
      & ( ~ r2_hidden(X34,X35)
        | r1_tarski(k1_tarski(X34),X35) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57])])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:18:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.72/1.90  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.72/1.90  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.72/1.90  #
% 1.72/1.90  # Preprocessing time       : 0.028 s
% 1.72/1.90  # Presaturation interreduction done
% 1.72/1.90  
% 1.72/1.90  # Proof found!
% 1.72/1.90  # SZS status Theorem
% 1.72/1.90  # SZS output start CNFRefutation
% 1.72/1.90  fof(t60_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X1))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_subset_1)).
% 1.72/1.90  fof(t59_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k3_enumset1(X2,X3,X4,X5,X6),k1_zfmisc_1(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_subset_1)).
% 1.72/1.90  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 1.72/1.90  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 1.72/1.90  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 1.72/1.90  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.72/1.90  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.72/1.90  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.72/1.90  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.72/1.90  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.72/1.90  fof(t37_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 1.72/1.90  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X1)))))))))), inference(assume_negation,[status(cth)],[t60_subset_1])).
% 1.72/1.90  fof(c_0_12, plain, ![X57, X58, X59, X60, X61, X62]:(~m1_subset_1(X58,X57)|(~m1_subset_1(X59,X57)|(~m1_subset_1(X60,X57)|(~m1_subset_1(X61,X57)|(~m1_subset_1(X62,X57)|(X57=k1_xboole_0|m1_subset_1(k3_enumset1(X58,X59,X60,X61,X62),k1_zfmisc_1(X57)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_subset_1])])])).
% 1.72/1.90  fof(c_0_13, negated_conjecture, (m1_subset_1(esk5_0,esk4_0)&(m1_subset_1(esk6_0,esk4_0)&(m1_subset_1(esk7_0,esk4_0)&(m1_subset_1(esk8_0,esk4_0)&(m1_subset_1(esk9_0,esk4_0)&(m1_subset_1(esk10_0,esk4_0)&(esk4_0!=k1_xboole_0&~m1_subset_1(k4_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),k1_zfmisc_1(esk4_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 1.72/1.90  fof(c_0_14, plain, ![X54, X55, X56]:(~m1_subset_1(X55,k1_zfmisc_1(X54))|(~r2_hidden(X56,X55)|r2_hidden(X56,X54))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 1.72/1.90  cnf(c_0_15, plain, (X2=k1_xboole_0|m1_subset_1(k3_enumset1(X1,X3,X4,X5,X6),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)|~m1_subset_1(X3,X2)|~m1_subset_1(X4,X2)|~m1_subset_1(X5,X2)|~m1_subset_1(X6,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.72/1.90  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk10_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.72/1.90  cnf(c_0_17, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.72/1.90  fof(c_0_18, plain, ![X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51]:(((~r2_hidden(X44,X43)|(X44=X38|X44=X39|X44=X40|X44=X41|X44=X42)|X43!=k3_enumset1(X38,X39,X40,X41,X42))&(((((X45!=X38|r2_hidden(X45,X43)|X43!=k3_enumset1(X38,X39,X40,X41,X42))&(X45!=X39|r2_hidden(X45,X43)|X43!=k3_enumset1(X38,X39,X40,X41,X42)))&(X45!=X40|r2_hidden(X45,X43)|X43!=k3_enumset1(X38,X39,X40,X41,X42)))&(X45!=X41|r2_hidden(X45,X43)|X43!=k3_enumset1(X38,X39,X40,X41,X42)))&(X45!=X42|r2_hidden(X45,X43)|X43!=k3_enumset1(X38,X39,X40,X41,X42))))&((((((esk3_6(X46,X47,X48,X49,X50,X51)!=X46|~r2_hidden(esk3_6(X46,X47,X48,X49,X50,X51),X51)|X51=k3_enumset1(X46,X47,X48,X49,X50))&(esk3_6(X46,X47,X48,X49,X50,X51)!=X47|~r2_hidden(esk3_6(X46,X47,X48,X49,X50,X51),X51)|X51=k3_enumset1(X46,X47,X48,X49,X50)))&(esk3_6(X46,X47,X48,X49,X50,X51)!=X48|~r2_hidden(esk3_6(X46,X47,X48,X49,X50,X51),X51)|X51=k3_enumset1(X46,X47,X48,X49,X50)))&(esk3_6(X46,X47,X48,X49,X50,X51)!=X49|~r2_hidden(esk3_6(X46,X47,X48,X49,X50,X51),X51)|X51=k3_enumset1(X46,X47,X48,X49,X50)))&(esk3_6(X46,X47,X48,X49,X50,X51)!=X50|~r2_hidden(esk3_6(X46,X47,X48,X49,X50,X51),X51)|X51=k3_enumset1(X46,X47,X48,X49,X50)))&(r2_hidden(esk3_6(X46,X47,X48,X49,X50,X51),X51)|(esk3_6(X46,X47,X48,X49,X50,X51)=X46|esk3_6(X46,X47,X48,X49,X50,X51)=X47|esk3_6(X46,X47,X48,X49,X50,X51)=X48|esk3_6(X46,X47,X48,X49,X50,X51)=X49|esk3_6(X46,X47,X48,X49,X50,X51)=X50)|X51=k3_enumset1(X46,X47,X48,X49,X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 1.72/1.90  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.72/1.90  cnf(c_0_20, negated_conjecture, (m1_subset_1(k3_enumset1(X1,X2,X3,X4,esk10_0),k1_zfmisc_1(esk4_0))|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 1.72/1.90  cnf(c_0_21, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X2,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.72/1.90  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X5,esk4_0)|~r2_hidden(X1,k3_enumset1(X5,X4,X3,X2,esk10_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.72/1.90  cnf(c_0_23, plain, (r2_hidden(X1,k3_enumset1(X2,X1,X3,X4,X5))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).
% 1.72/1.90  fof(c_0_24, plain, ![X15, X16, X17, X18, X19, X20]:k4_enumset1(X15,X16,X17,X18,X19,X20)=k2_xboole_0(k1_tarski(X15),k3_enumset1(X16,X17,X18,X19,X20)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 1.72/1.90  fof(c_0_25, plain, ![X36, X37]:(((~m1_subset_1(X37,X36)|r2_hidden(X37,X36)|v1_xboole_0(X36))&(~r2_hidden(X37,X36)|m1_subset_1(X37,X36)|v1_xboole_0(X36)))&((~m1_subset_1(X37,X36)|v1_xboole_0(X37)|~v1_xboole_0(X36))&(~v1_xboole_0(X37)|m1_subset_1(X37,X36)|~v1_xboole_0(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 1.72/1.90  fof(c_0_26, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 1.72/1.90  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X4,esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.72/1.90  cnf(c_0_28, negated_conjecture, (~m1_subset_1(k4_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.72/1.90  cnf(c_0_29, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.72/1.90  cnf(c_0_30, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.72/1.90  cnf(c_0_31, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.72/1.90  fof(c_0_32, plain, ![X27, X28, X29, X30, X31, X32]:(((~r2_hidden(X29,X28)|r1_tarski(X29,X27)|X28!=k1_zfmisc_1(X27))&(~r1_tarski(X30,X27)|r2_hidden(X30,X28)|X28!=k1_zfmisc_1(X27)))&((~r2_hidden(esk2_2(X31,X32),X32)|~r1_tarski(esk2_2(X31,X32),X31)|X32=k1_zfmisc_1(X31))&(r2_hidden(esk2_2(X31,X32),X32)|r1_tarski(esk2_2(X31,X32),X31)|X32=k1_zfmisc_1(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 1.72/1.90  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X3,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_16])).
% 1.72/1.90  cnf(c_0_34, negated_conjecture, (~m1_subset_1(k2_xboole_0(k1_tarski(esk5_0),k3_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)),k1_zfmisc_1(esk4_0))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 1.72/1.90  cnf(c_0_35, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_30, c_0_31])).
% 1.72/1.90  cnf(c_0_36, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.72/1.90  fof(c_0_37, plain, ![X53]:~v1_xboole_0(k1_zfmisc_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 1.72/1.90  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_16])).
% 1.72/1.90  cnf(c_0_39, negated_conjecture, (~r2_hidden(k2_xboole_0(k1_tarski(esk5_0),k3_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.72/1.90  cnf(c_0_40, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_36])).
% 1.72/1.90  fof(c_0_41, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X14,X13)|r1_tarski(k2_xboole_0(X12,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 1.72/1.90  cnf(c_0_42, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.72/1.90  cnf(c_0_43, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.72/1.90  cnf(c_0_44, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.72/1.90  cnf(c_0_45, negated_conjecture, (r2_hidden(esk10_0,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_16])).
% 1.72/1.90  cnf(c_0_46, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_tarski(esk5_0),k3_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)),esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.72/1.90  cnf(c_0_47, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.72/1.90  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_42])).
% 1.72/1.90  cnf(c_0_49, negated_conjecture, (r2_hidden(k3_enumset1(X1,X2,X3,X4,esk10_0),k1_zfmisc_1(esk4_0))|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_20]), c_0_44])).
% 1.72/1.90  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.72/1.90  cnf(c_0_51, negated_conjecture, (r2_hidden(esk10_0,esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_16])).
% 1.72/1.90  cnf(c_0_52, negated_conjecture, (~r1_tarski(k3_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0),esk4_0)|~r1_tarski(k1_tarski(esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.72/1.90  cnf(c_0_53, negated_conjecture, (r1_tarski(k3_enumset1(X1,X2,X3,X4,esk10_0),esk4_0)|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.72/1.90  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk9_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.72/1.90  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk8_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.72/1.90  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.72/1.90  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.72/1.90  fof(c_0_58, plain, ![X34, X35]:((~r1_tarski(k1_tarski(X34),X35)|r2_hidden(X34,X35))&(~r2_hidden(X34,X35)|r1_tarski(k1_tarski(X34),X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).
% 1.72/1.90  cnf(c_0_59, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_50])).
% 1.72/1.90  cnf(c_0_60, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_51])).
% 1.72/1.90  cnf(c_0_61, negated_conjecture, (~r1_tarski(k1_tarski(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57])])).
% 1.72/1.90  cnf(c_0_62, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.72/1.90  cnf(c_0_63, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(sr,[status(thm)],[c_0_59, c_0_60])).
% 1.72/1.90  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])]), ['proof']).
% 1.72/1.90  # SZS output end CNFRefutation
% 1.72/1.90  # Proof object total steps             : 65
% 1.72/1.90  # Proof object clause steps            : 42
% 1.72/1.90  # Proof object formula steps           : 23
% 1.72/1.90  # Proof object conjectures             : 29
% 1.72/1.90  # Proof object clause conjectures      : 26
% 1.72/1.90  # Proof object formula conjectures     : 3
% 1.72/1.90  # Proof object initial clauses used    : 20
% 1.72/1.90  # Proof object initial formulas used   : 11
% 1.72/1.90  # Proof object generating inferences   : 16
% 1.72/1.90  # Proof object simplifying inferences  : 16
% 1.72/1.90  # Training examples: 0 positive, 0 negative
% 1.72/1.90  # Parsed axioms                        : 12
% 1.72/1.90  # Removed by relevancy pruning/SinE    : 0
% 1.72/1.90  # Initial clauses                      : 38
% 1.72/1.90  # Removed in clause preprocessing      : 1
% 1.72/1.90  # Initial clauses in saturation        : 37
% 1.72/1.90  # Processed clauses                    : 11639
% 1.72/1.90  # ...of these trivial                  : 6
% 1.72/1.90  # ...subsumed                          : 8571
% 1.72/1.90  # ...remaining for further processing  : 3062
% 1.72/1.90  # Other redundant clauses eliminated   : 288
% 1.72/1.90  # Clauses deleted for lack of memory   : 0
% 1.72/1.90  # Backward-subsumed                    : 200
% 1.72/1.90  # Backward-rewritten                   : 2434
% 1.72/1.90  # Generated clauses                    : 85709
% 1.72/1.90  # ...of the previous two non-trivial   : 84954
% 1.72/1.90  # Contextual simplify-reflections      : 797
% 1.72/1.90  # Paramodulations                      : 85189
% 1.72/1.90  # Factorizations                       : 232
% 1.72/1.90  # Equation resolutions                 : 288
% 1.72/1.90  # Propositional unsat checks           : 0
% 1.72/1.90  #    Propositional check models        : 0
% 1.72/1.90  #    Propositional check unsatisfiable : 0
% 1.72/1.90  #    Propositional clauses             : 0
% 1.72/1.90  #    Propositional clauses after purity: 0
% 1.72/1.90  #    Propositional unsat core size     : 0
% 1.72/1.90  #    Propositional preprocessing time  : 0.000
% 1.72/1.90  #    Propositional encoding time       : 0.000
% 1.72/1.90  #    Propositional solver time         : 0.000
% 1.72/1.90  #    Success case prop preproc time    : 0.000
% 1.72/1.90  #    Success case prop encoding time   : 0.000
% 1.72/1.90  #    Success case prop solver time     : 0.000
% 1.72/1.90  # Current number of processed clauses  : 378
% 1.72/1.90  #    Positive orientable unit clauses  : 19
% 1.72/1.90  #    Positive unorientable unit clauses: 0
% 1.72/1.90  #    Negative unit clauses             : 8
% 1.72/1.90  #    Non-unit-clauses                  : 351
% 1.72/1.90  # Current number of unprocessed clauses: 45638
% 1.72/1.90  # ...number of literals in the above   : 289681
% 1.72/1.90  # Current number of archived formulas  : 0
% 1.72/1.90  # Current number of archived clauses   : 2677
% 1.72/1.90  # Clause-clause subsumption calls (NU) : 7735610
% 1.72/1.90  # Rec. Clause-clause subsumption calls : 2830096
% 1.72/1.90  # Non-unit clause-clause subsumptions  : 9393
% 1.72/1.90  # Unit Clause-clause subsumption calls : 6288
% 1.72/1.90  # Rewrite failures with RHS unbound    : 0
% 1.72/1.90  # BW rewrite match attempts            : 26
% 1.72/1.90  # BW rewrite match successes           : 6
% 1.72/1.90  # Condensation attempts                : 0
% 1.72/1.90  # Condensation successes               : 0
% 1.72/1.90  # Termbank termtop insertions          : 1815359
% 1.72/1.91  
% 1.72/1.91  # -------------------------------------------------
% 1.72/1.91  # User time                : 1.504 s
% 1.72/1.91  # System time              : 0.040 s
% 1.72/1.91  # Total time               : 1.543 s
% 1.72/1.91  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
