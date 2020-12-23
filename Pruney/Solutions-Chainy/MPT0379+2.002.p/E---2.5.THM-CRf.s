%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:53 EST 2020

% Result     : Theorem 6.33s
% Output     : CNFRefutation 6.33s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 133 expanded)
%              Number of clauses        :   44 (  55 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  272 ( 776 expanded)
%              Number of equality atoms :   64 ( 118 expanded)
%              Maximal formula depth    :   37 (   6 average)
%              Maximal clause size      :   52 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_subset_1,conjecture,(
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
                         => ! [X8] :
                              ( m1_subset_1(X8,X1)
                             => ( X1 != k1_xboole_0
                               => m1_subset_1(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_subset_1)).

fof(t60_subset_1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(t56_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

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
                           => ! [X8] :
                                ( m1_subset_1(X8,X1)
                               => ( X1 != k1_xboole_0
                                 => m1_subset_1(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X1)) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_subset_1])).

fof(c_0_12,plain,(
    ! [X62,X63,X64,X65,X66,X67,X68] :
      ( ~ m1_subset_1(X63,X62)
      | ~ m1_subset_1(X64,X62)
      | ~ m1_subset_1(X65,X62)
      | ~ m1_subset_1(X66,X62)
      | ~ m1_subset_1(X67,X62)
      | ~ m1_subset_1(X68,X62)
      | X62 = k1_xboole_0
      | m1_subset_1(k4_enumset1(X63,X64,X65,X66,X67,X68),k1_zfmisc_1(X62)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_subset_1])])])).

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,esk4_0)
    & m1_subset_1(esk6_0,esk4_0)
    & m1_subset_1(esk7_0,esk4_0)
    & m1_subset_1(esk8_0,esk4_0)
    & m1_subset_1(esk9_0,esk4_0)
    & m1_subset_1(esk10_0,esk4_0)
    & m1_subset_1(esk11_0,esk4_0)
    & esk4_0 != k1_xboole_0
    & ~ m1_subset_1(k5_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),k1_zfmisc_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X59,X60,X61] :
      ( ~ m1_subset_1(X60,k1_zfmisc_1(X59))
      | ~ r2_hidden(X61,X60)
      | r2_hidden(X61,X59) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_15,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k4_enumset1(X1,X3,X4,X5,X6,X7),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,X2)
    | ~ m1_subset_1(X4,X2)
    | ~ m1_subset_1(X5,X2)
    | ~ m1_subset_1(X6,X2)
    | ~ m1_subset_1(X7,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk11_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56] :
      ( ( ~ r2_hidden(X48,X47)
        | X48 = X41
        | X48 = X42
        | X48 = X43
        | X48 = X44
        | X48 = X45
        | X48 = X46
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( X49 != X41
        | r2_hidden(X49,X47)
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( X49 != X42
        | r2_hidden(X49,X47)
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( X49 != X43
        | r2_hidden(X49,X47)
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( X49 != X44
        | r2_hidden(X49,X47)
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( X49 != X45
        | r2_hidden(X49,X47)
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( X49 != X46
        | r2_hidden(X49,X47)
        | X47 != k4_enumset1(X41,X42,X43,X44,X45,X46) )
      & ( esk3_7(X50,X51,X52,X53,X54,X55,X56) != X50
        | ~ r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) )
      & ( esk3_7(X50,X51,X52,X53,X54,X55,X56) != X51
        | ~ r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) )
      & ( esk3_7(X50,X51,X52,X53,X54,X55,X56) != X52
        | ~ r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) )
      & ( esk3_7(X50,X51,X52,X53,X54,X55,X56) != X53
        | ~ r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) )
      & ( esk3_7(X50,X51,X52,X53,X54,X55,X56) != X54
        | ~ r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) )
      & ( esk3_7(X50,X51,X52,X53,X54,X55,X56) != X55
        | ~ r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) )
      & ( r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)
        | esk3_7(X50,X51,X52,X53,X54,X55,X56) = X50
        | esk3_7(X50,X51,X52,X53,X54,X55,X56) = X51
        | esk3_7(X50,X51,X52,X53,X54,X55,X56) = X52
        | esk3_7(X50,X51,X52,X53,X54,X55,X56) = X53
        | esk3_7(X50,X51,X52,X53,X54,X55,X56) = X54
        | esk3_7(X50,X51,X52,X53,X54,X55,X56) = X55
        | X56 = k4_enumset1(X50,X51,X52,X53,X54,X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,esk11_0),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(X5,esk4_0)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X5,X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X5,esk4_0)
    | ~ m1_subset_1(X6,esk4_0)
    | ~ r2_hidden(X1,k4_enumset1(X6,X5,X4,X3,X2,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X3,X4,X5,X6,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk11_0,esk4_0)
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X5,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_25,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22] : k5_enumset1(X16,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k1_tarski(X16),k4_enumset1(X17,X18,X19,X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[t56_enumset1])).

fof(c_0_26,plain,(
    ! [X39,X40] :
      ( ( ~ m1_subset_1(X40,X39)
        | r2_hidden(X40,X39)
        | v1_xboole_0(X39) )
      & ( ~ r2_hidden(X40,X39)
        | m1_subset_1(X40,X39)
        | v1_xboole_0(X39) )
      & ( ~ m1_subset_1(X40,X39)
        | v1_xboole_0(X40)
        | ~ v1_xboole_0(X39) )
      & ( ~ v1_xboole_0(X40)
        | m1_subset_1(X40,X39)
        | ~ v1_xboole_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_27,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk11_0,esk4_0)
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X4,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( ~ m1_subset_1(k5_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ( ~ r2_hidden(X32,X31)
        | r1_tarski(X32,X30)
        | X31 != k1_zfmisc_1(X30) )
      & ( ~ r1_tarski(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k1_zfmisc_1(X30) )
      & ( ~ r2_hidden(esk2_2(X34,X35),X35)
        | ~ r1_tarski(esk2_2(X34,X35),X34)
        | X35 = k1_zfmisc_1(X34) )
      & ( r2_hidden(esk2_2(X34,X35),X35)
        | r1_tarski(esk2_2(X34,X35),X34)
        | X35 = k1_zfmisc_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk11_0,esk4_0)
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X3,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(k1_tarski(esk5_0),k4_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0)),k1_zfmisc_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,plain,(
    ! [X58] : ~ v1_xboole_0(k1_zfmisc_1(X58)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk11_0,esk4_0)
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(esk5_0),k4_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_37])).

fof(c_0_42,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X15,X14)
      | r1_tarski(k2_xboole_0(X13,X15),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_45,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk11_0,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(esk5_0),k4_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_enumset1(X1,X2,X3,X4,X5,esk11_0),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(X5,esk4_0)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_20]),c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk11_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k4_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),esk4_0)
    | ~ r1_tarski(k1_tarski(esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k4_enumset1(X1,X2,X3,X4,X5,esk11_0),esk4_0)
    | ~ m1_subset_1(X5,esk4_0)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk10_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk9_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk8_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_60,plain,(
    ! [X37,X38] :
      ( ( ~ r1_tarski(k1_tarski(X37),X38)
        | r2_hidden(X37,X38) )
      & ( ~ r2_hidden(X37,X38)
        | r1_tarski(k1_tarski(X37),X38) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59])])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:32:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 6.33/6.51  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 6.33/6.51  # and selection function SelectComplexExceptUniqMaxHorn.
% 6.33/6.51  #
% 6.33/6.51  # Preprocessing time       : 0.029 s
% 6.33/6.51  # Presaturation interreduction done
% 6.33/6.51  
% 6.33/6.51  # Proof found!
% 6.33/6.51  # SZS status Theorem
% 6.33/6.51  # SZS output start CNFRefutation
% 6.33/6.51  fof(t61_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X1)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_subset_1)).
% 6.33/6.51  fof(t60_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X1))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_subset_1)).
% 6.33/6.51  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.33/6.51  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 6.33/6.51  fof(t56_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 6.33/6.51  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.33/6.51  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.33/6.51  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.33/6.51  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.33/6.51  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.33/6.51  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.33/6.51  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X1))))))))))), inference(assume_negation,[status(cth)],[t61_subset_1])).
% 6.33/6.51  fof(c_0_12, plain, ![X62, X63, X64, X65, X66, X67, X68]:(~m1_subset_1(X63,X62)|(~m1_subset_1(X64,X62)|(~m1_subset_1(X65,X62)|(~m1_subset_1(X66,X62)|(~m1_subset_1(X67,X62)|(~m1_subset_1(X68,X62)|(X62=k1_xboole_0|m1_subset_1(k4_enumset1(X63,X64,X65,X66,X67,X68),k1_zfmisc_1(X62))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_subset_1])])])).
% 6.33/6.51  fof(c_0_13, negated_conjecture, (m1_subset_1(esk5_0,esk4_0)&(m1_subset_1(esk6_0,esk4_0)&(m1_subset_1(esk7_0,esk4_0)&(m1_subset_1(esk8_0,esk4_0)&(m1_subset_1(esk9_0,esk4_0)&(m1_subset_1(esk10_0,esk4_0)&(m1_subset_1(esk11_0,esk4_0)&(esk4_0!=k1_xboole_0&~m1_subset_1(k5_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),k1_zfmisc_1(esk4_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 6.33/6.51  fof(c_0_14, plain, ![X59, X60, X61]:(~m1_subset_1(X60,k1_zfmisc_1(X59))|(~r2_hidden(X61,X60)|r2_hidden(X61,X59))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 6.33/6.51  cnf(c_0_15, plain, (X2=k1_xboole_0|m1_subset_1(k4_enumset1(X1,X3,X4,X5,X6,X7),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)|~m1_subset_1(X3,X2)|~m1_subset_1(X4,X2)|~m1_subset_1(X5,X2)|~m1_subset_1(X6,X2)|~m1_subset_1(X7,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 6.33/6.51  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk11_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.33/6.51  cnf(c_0_17, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.33/6.51  fof(c_0_18, plain, ![X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56]:(((~r2_hidden(X48,X47)|(X48=X41|X48=X42|X48=X43|X48=X44|X48=X45|X48=X46)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46))&((((((X49!=X41|r2_hidden(X49,X47)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46))&(X49!=X42|r2_hidden(X49,X47)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46)))&(X49!=X43|r2_hidden(X49,X47)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46)))&(X49!=X44|r2_hidden(X49,X47)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46)))&(X49!=X45|r2_hidden(X49,X47)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46)))&(X49!=X46|r2_hidden(X49,X47)|X47!=k4_enumset1(X41,X42,X43,X44,X45,X46))))&(((((((esk3_7(X50,X51,X52,X53,X54,X55,X56)!=X50|~r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55))&(esk3_7(X50,X51,X52,X53,X54,X55,X56)!=X51|~r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55)))&(esk3_7(X50,X51,X52,X53,X54,X55,X56)!=X52|~r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55)))&(esk3_7(X50,X51,X52,X53,X54,X55,X56)!=X53|~r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55)))&(esk3_7(X50,X51,X52,X53,X54,X55,X56)!=X54|~r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55)))&(esk3_7(X50,X51,X52,X53,X54,X55,X56)!=X55|~r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55)))&(r2_hidden(esk3_7(X50,X51,X52,X53,X54,X55,X56),X56)|(esk3_7(X50,X51,X52,X53,X54,X55,X56)=X50|esk3_7(X50,X51,X52,X53,X54,X55,X56)=X51|esk3_7(X50,X51,X52,X53,X54,X55,X56)=X52|esk3_7(X50,X51,X52,X53,X54,X55,X56)=X53|esk3_7(X50,X51,X52,X53,X54,X55,X56)=X54|esk3_7(X50,X51,X52,X53,X54,X55,X56)=X55)|X56=k4_enumset1(X50,X51,X52,X53,X54,X55)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 6.33/6.51  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.33/6.51  cnf(c_0_20, negated_conjecture, (m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,esk11_0),k1_zfmisc_1(esk4_0))|~m1_subset_1(X5,esk4_0)|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 6.33/6.51  cnf(c_0_21, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X5,X6,X7,X8,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.33/6.51  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X5,esk4_0)|~m1_subset_1(X6,esk4_0)|~r2_hidden(X1,k4_enumset1(X6,X5,X4,X3,X2,esk11_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 6.33/6.51  cnf(c_0_23, plain, (r2_hidden(X1,k4_enumset1(X2,X3,X4,X5,X6,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).
% 6.33/6.51  cnf(c_0_24, negated_conjecture, (r2_hidden(esk11_0,esk4_0)|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X5,esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 6.33/6.51  fof(c_0_25, plain, ![X16, X17, X18, X19, X20, X21, X22]:k5_enumset1(X16,X17,X18,X19,X20,X21,X22)=k2_xboole_0(k1_tarski(X16),k4_enumset1(X17,X18,X19,X20,X21,X22)), inference(variable_rename,[status(thm)],[t56_enumset1])).
% 6.33/6.51  fof(c_0_26, plain, ![X39, X40]:(((~m1_subset_1(X40,X39)|r2_hidden(X40,X39)|v1_xboole_0(X39))&(~r2_hidden(X40,X39)|m1_subset_1(X40,X39)|v1_xboole_0(X39)))&((~m1_subset_1(X40,X39)|v1_xboole_0(X40)|~v1_xboole_0(X39))&(~v1_xboole_0(X40)|m1_subset_1(X40,X39)|~v1_xboole_0(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 6.33/6.51  fof(c_0_27, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 6.33/6.51  cnf(c_0_28, negated_conjecture, (r2_hidden(esk11_0,esk4_0)|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X4,esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_16])).
% 6.33/6.51  cnf(c_0_29, negated_conjecture, (~m1_subset_1(k5_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.33/6.51  cnf(c_0_30, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 6.33/6.51  cnf(c_0_31, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.33/6.51  cnf(c_0_32, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 6.33/6.51  fof(c_0_33, plain, ![X30, X31, X32, X33, X34, X35]:(((~r2_hidden(X32,X31)|r1_tarski(X32,X30)|X31!=k1_zfmisc_1(X30))&(~r1_tarski(X33,X30)|r2_hidden(X33,X31)|X31!=k1_zfmisc_1(X30)))&((~r2_hidden(esk2_2(X34,X35),X35)|~r1_tarski(esk2_2(X34,X35),X34)|X35=k1_zfmisc_1(X34))&(r2_hidden(esk2_2(X34,X35),X35)|r1_tarski(esk2_2(X34,X35),X34)|X35=k1_zfmisc_1(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 6.33/6.51  cnf(c_0_34, negated_conjecture, (r2_hidden(esk11_0,esk4_0)|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X3,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_16])).
% 6.33/6.51  cnf(c_0_35, negated_conjecture, (~m1_subset_1(k2_xboole_0(k1_tarski(esk5_0),k4_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0)),k1_zfmisc_1(esk4_0))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 6.33/6.51  cnf(c_0_36, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_31, c_0_32])).
% 6.33/6.51  cnf(c_0_37, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 6.33/6.51  fof(c_0_38, plain, ![X58]:~v1_xboole_0(k1_zfmisc_1(X58)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 6.33/6.51  cnf(c_0_39, negated_conjecture, (r2_hidden(esk11_0,esk4_0)|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_16])).
% 6.33/6.51  cnf(c_0_40, negated_conjecture, (~r2_hidden(k2_xboole_0(k1_tarski(esk5_0),k4_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 6.33/6.51  cnf(c_0_41, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_37])).
% 6.33/6.51  fof(c_0_42, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X15,X14)|r1_tarski(k2_xboole_0(X13,X15),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 6.33/6.51  cnf(c_0_43, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 6.33/6.51  cnf(c_0_44, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.33/6.51  cnf(c_0_45, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 6.33/6.51  cnf(c_0_46, negated_conjecture, (r2_hidden(esk11_0,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_16])).
% 6.33/6.51  cnf(c_0_47, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_tarski(esk5_0),k4_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0)),esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 6.33/6.51  cnf(c_0_48, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 6.33/6.51  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_43])).
% 6.33/6.51  cnf(c_0_50, negated_conjecture, (r2_hidden(k4_enumset1(X1,X2,X3,X4,X5,esk11_0),k1_zfmisc_1(esk4_0))|~m1_subset_1(X5,esk4_0)|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_20]), c_0_45])).
% 6.33/6.51  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.33/6.51  cnf(c_0_52, negated_conjecture, (r2_hidden(esk11_0,esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_16])).
% 6.33/6.51  cnf(c_0_53, negated_conjecture, (~r1_tarski(k4_enumset1(esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),esk4_0)|~r1_tarski(k1_tarski(esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 6.33/6.51  cnf(c_0_54, negated_conjecture, (r1_tarski(k4_enumset1(X1,X2,X3,X4,X5,esk11_0),esk4_0)|~m1_subset_1(X5,esk4_0)|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 6.33/6.51  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk10_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.33/6.51  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk9_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.33/6.51  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk8_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.33/6.51  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.33/6.51  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.33/6.51  fof(c_0_60, plain, ![X37, X38]:((~r1_tarski(k1_tarski(X37),X38)|r2_hidden(X37,X38))&(~r2_hidden(X37,X38)|r1_tarski(k1_tarski(X37),X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 6.33/6.51  cnf(c_0_61, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_51])).
% 6.33/6.51  cnf(c_0_62, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_52])).
% 6.33/6.51  cnf(c_0_63, negated_conjecture, (~r1_tarski(k1_tarski(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58]), c_0_59])])).
% 6.33/6.51  cnf(c_0_64, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 6.33/6.51  cnf(c_0_65, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(sr,[status(thm)],[c_0_61, c_0_62])).
% 6.33/6.52  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])]), ['proof']).
% 6.33/6.52  # SZS output end CNFRefutation
% 6.33/6.52  # Proof object total steps             : 67
% 6.33/6.52  # Proof object clause steps            : 44
% 6.33/6.52  # Proof object formula steps           : 23
% 6.33/6.52  # Proof object conjectures             : 31
% 6.33/6.52  # Proof object clause conjectures      : 28
% 6.33/6.52  # Proof object formula conjectures     : 3
% 6.33/6.52  # Proof object initial clauses used    : 21
% 6.33/6.52  # Proof object initial formulas used   : 11
% 6.33/6.52  # Proof object generating inferences   : 17
% 6.33/6.52  # Proof object simplifying inferences  : 17
% 6.33/6.52  # Training examples: 0 positive, 0 negative
% 6.33/6.52  # Parsed axioms                        : 12
% 6.33/6.52  # Removed by relevancy pruning/SinE    : 0
% 6.33/6.52  # Initial clauses                      : 41
% 6.33/6.52  # Removed in clause preprocessing      : 1
% 6.33/6.52  # Initial clauses in saturation        : 40
% 6.33/6.52  # Processed clauses                    : 30140
% 6.33/6.52  # ...of these trivial                  : 0
% 6.33/6.52  # ...subsumed                          : 23088
% 6.33/6.52  # ...remaining for further processing  : 7052
% 6.33/6.52  # Other redundant clauses eliminated   : 1203
% 6.33/6.52  # Clauses deleted for lack of memory   : 0
% 6.33/6.52  # Backward-subsumed                    : 335
% 6.33/6.52  # Backward-rewritten                   : 5779
% 6.33/6.52  # Generated clauses                    : 374060
% 6.33/6.52  # ...of the previous two non-trivial   : 371928
% 6.33/6.52  # Contextual simplify-reflections      : 2825
% 6.33/6.52  # Paramodulations                      : 371724
% 6.33/6.52  # Factorizations                       : 1133
% 6.33/6.52  # Equation resolutions                 : 1203
% 6.33/6.52  # Propositional unsat checks           : 1
% 6.33/6.52  #    Propositional check models        : 1
% 6.33/6.52  #    Propositional check unsatisfiable : 0
% 6.33/6.52  #    Propositional clauses             : 0
% 6.33/6.52  #    Propositional clauses after purity: 0
% 6.33/6.52  #    Propositional unsat core size     : 0
% 6.33/6.52  #    Propositional preprocessing time  : 0.000
% 6.33/6.52  #    Propositional encoding time       : 0.136
% 6.33/6.52  #    Propositional solver time         : 0.006
% 6.33/6.52  #    Success case prop preproc time    : 0.000
% 6.33/6.52  #    Success case prop encoding time   : 0.000
% 6.33/6.52  #    Success case prop solver time     : 0.000
% 6.33/6.52  # Current number of processed clauses  : 883
% 6.33/6.52  #    Positive orientable unit clauses  : 22
% 6.33/6.52  #    Positive unorientable unit clauses: 0
% 6.33/6.52  #    Negative unit clauses             : 8
% 6.33/6.52  #    Non-unit-clauses                  : 853
% 6.33/6.52  # Current number of unprocessed clauses: 284139
% 6.33/6.52  # ...number of literals in the above   : 1894832
% 6.33/6.52  # Current number of archived formulas  : 0
% 6.33/6.52  # Current number of archived clauses   : 6161
% 6.33/6.52  # Clause-clause subsumption calls (NU) : 38040419
% 6.33/6.52  # Rec. Clause-clause subsumption calls : 13484463
% 6.33/6.52  # Non-unit clause-clause subsumptions  : 25906
% 6.33/6.52  # Unit Clause-clause subsumption calls : 15127
% 6.33/6.52  # Rewrite failures with RHS unbound    : 0
% 6.33/6.52  # BW rewrite match attempts            : 37
% 6.33/6.52  # BW rewrite match successes           : 7
% 6.33/6.52  # Condensation attempts                : 0
% 6.33/6.52  # Condensation successes               : 0
% 6.33/6.52  # Termbank termtop insertions          : 11307347
% 6.33/6.53  
% 6.33/6.53  # -------------------------------------------------
% 6.33/6.53  # User time                : 6.025 s
% 6.33/6.53  # System time              : 0.158 s
% 6.33/6.53  # Total time               : 6.184 s
% 6.33/6.53  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
