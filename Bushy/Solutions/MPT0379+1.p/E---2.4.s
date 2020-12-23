%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t61_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:26 EDT 2019

% Result     : Theorem 264.40s
% Output     : CNFRefutation 264.40s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 285 expanded)
%              Number of clauses        :   40 ( 125 expanded)
%              Number of leaves         :    7 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  246 (1468 expanded)
%              Number of equality atoms :  116 ( 251 expanded)
%              Maximal formula depth    :   42 (   5 average)
%              Maximal clause size      :   60 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',d1_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',t61_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',t7_boole)).

fof(d5_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( X8 = k5_enumset1(X1,X2,X3,X4,X5,X6,X7)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X9 != X1
              & X9 != X2
              & X9 != X3
              & X9 != X4
              & X9 != X5
              & X9 != X6
              & X9 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',d5_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',d3_tarski)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t61_subset_1.p',t6_boole)).

fof(c_0_7,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | r1_tarski(X22,X20)
        | X21 != k1_zfmisc_1(X20) )
      & ( ~ r1_tarski(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k1_zfmisc_1(X20) )
      & ( ~ r2_hidden(esk9_2(X24,X25),X25)
        | ~ r1_tarski(esk9_2(X24,X25),X24)
        | X25 = k1_zfmisc_1(X24) )
      & ( r2_hidden(esk9_2(X24,X25),X25)
        | r1_tarski(esk9_2(X24,X25),X24)
        | X25 = k1_zfmisc_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X28,X27)
        | r2_hidden(X28,X27)
        | v1_xboole_0(X27) )
      & ( ~ r2_hidden(X28,X27)
        | m1_subset_1(X28,X27)
        | v1_xboole_0(X27) )
      & ( ~ m1_subset_1(X28,X27)
        | v1_xboole_0(X28)
        | ~ v1_xboole_0(X27) )
      & ( ~ v1_xboole_0(X28)
        | m1_subset_1(X28,X27)
        | ~ v1_xboole_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_10,plain,(
    ! [X57,X58] :
      ( ~ r2_hidden(X57,X58)
      | ~ v1_xboole_0(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_11,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52] :
      ( ( ~ r2_hidden(X43,X42)
        | X43 = X35
        | X43 = X36
        | X43 = X37
        | X43 = X38
        | X43 = X39
        | X43 = X40
        | X43 = X41
        | X42 != k5_enumset1(X35,X36,X37,X38,X39,X40,X41) )
      & ( X44 != X35
        | r2_hidden(X44,X42)
        | X42 != k5_enumset1(X35,X36,X37,X38,X39,X40,X41) )
      & ( X44 != X36
        | r2_hidden(X44,X42)
        | X42 != k5_enumset1(X35,X36,X37,X38,X39,X40,X41) )
      & ( X44 != X37
        | r2_hidden(X44,X42)
        | X42 != k5_enumset1(X35,X36,X37,X38,X39,X40,X41) )
      & ( X44 != X38
        | r2_hidden(X44,X42)
        | X42 != k5_enumset1(X35,X36,X37,X38,X39,X40,X41) )
      & ( X44 != X39
        | r2_hidden(X44,X42)
        | X42 != k5_enumset1(X35,X36,X37,X38,X39,X40,X41) )
      & ( X44 != X40
        | r2_hidden(X44,X42)
        | X42 != k5_enumset1(X35,X36,X37,X38,X39,X40,X41) )
      & ( X44 != X41
        | r2_hidden(X44,X42)
        | X42 != k5_enumset1(X35,X36,X37,X38,X39,X40,X41) )
      & ( esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) != X45
        | ~ r2_hidden(esk11_8(X45,X46,X47,X48,X49,X50,X51,X52),X52)
        | X52 = k5_enumset1(X45,X46,X47,X48,X49,X50,X51) )
      & ( esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) != X46
        | ~ r2_hidden(esk11_8(X45,X46,X47,X48,X49,X50,X51,X52),X52)
        | X52 = k5_enumset1(X45,X46,X47,X48,X49,X50,X51) )
      & ( esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) != X47
        | ~ r2_hidden(esk11_8(X45,X46,X47,X48,X49,X50,X51,X52),X52)
        | X52 = k5_enumset1(X45,X46,X47,X48,X49,X50,X51) )
      & ( esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) != X48
        | ~ r2_hidden(esk11_8(X45,X46,X47,X48,X49,X50,X51,X52),X52)
        | X52 = k5_enumset1(X45,X46,X47,X48,X49,X50,X51) )
      & ( esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) != X49
        | ~ r2_hidden(esk11_8(X45,X46,X47,X48,X49,X50,X51,X52),X52)
        | X52 = k5_enumset1(X45,X46,X47,X48,X49,X50,X51) )
      & ( esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) != X50
        | ~ r2_hidden(esk11_8(X45,X46,X47,X48,X49,X50,X51,X52),X52)
        | X52 = k5_enumset1(X45,X46,X47,X48,X49,X50,X51) )
      & ( esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) != X51
        | ~ r2_hidden(esk11_8(X45,X46,X47,X48,X49,X50,X51,X52),X52)
        | X52 = k5_enumset1(X45,X46,X47,X48,X49,X50,X51) )
      & ( r2_hidden(esk11_8(X45,X46,X47,X48,X49,X50,X51,X52),X52)
        | esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) = X45
        | esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) = X46
        | esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) = X47
        | esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) = X48
        | esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) = X49
        | esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) = X50
        | esk11_8(X45,X46,X47,X48,X49,X50,X51,X52) = X51
        | X52 = k5_enumset1(X45,X46,X47,X48,X49,X50,X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X29,X30,X31,X32,X33] :
      ( ( ~ r1_tarski(X29,X30)
        | ~ r2_hidden(X31,X29)
        | r2_hidden(X31,X30) )
      & ( r2_hidden(esk10_2(X32,X33),X32)
        | r1_tarski(X32,X33) )
      & ( ~ r2_hidden(esk10_2(X32,X33),X33)
        | r1_tarski(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,esk1_0)
    & m1_subset_1(esk4_0,esk1_0)
    & m1_subset_1(esk5_0,esk1_0)
    & m1_subset_1(esk6_0,esk1_0)
    & m1_subset_1(esk7_0,esk1_0)
    & m1_subset_1(esk8_0,esk1_0)
    & esk1_0 != k1_xboole_0
    & ~ m1_subset_1(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_zfmisc_1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | X1 = X8
    | X1 = X9
    | ~ r2_hidden(X1,X2)
    | X2 != k5_enumset1(X3,X4,X5,X6,X7,X8,X9) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X56] :
      ( ~ v1_xboole_0(X56)
      | X56 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_21,negated_conjecture,
    ( ~ m1_subset_1(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | X1 = X8
    | ~ r2_hidden(X1,k5_enumset1(X8,X7,X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk10_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( esk10_2(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),X8) = X1
    | esk10_2(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),X8) = X2
    | esk10_2(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),X8) = X3
    | esk10_2(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),X8) = X4
    | esk10_2(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),X8) = X5
    | esk10_2(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),X8) = X6
    | esk10_2(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),X8) = X7
    | r2_hidden(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X8)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk8_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(esk10_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk8_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk7_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk6_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk5_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk4_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk3_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk8_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk2_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk3_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk4_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk5_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk6_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])]),c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk7_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_36]),c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk6_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk6_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk5_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk4_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk3_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_37]),c_0_38])]),c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_39]),c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk2_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk3_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk4_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_40]),c_0_41])]),c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk5_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_42]),c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_46,negated_conjecture,
    ( esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk4_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk3_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_43]),c_0_44])]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_45]),c_0_32])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk2_0
    | esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_46]),c_0_47])]),c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_48]),c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( esk10_2(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk1_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_49]),c_0_50])]),c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_51]),c_0_32])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_52]),c_0_53])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
