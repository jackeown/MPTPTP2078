%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0888+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:21 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 346 expanded)
%              Number of clauses        :   25 ( 119 expanded)
%              Number of leaves         :    8 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  222 (1640 expanded)
%              Number of equality atoms :  151 (1219 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(d7_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X3)
                 => ( X5 = k7_mcart_1(X1,X2,X3,X4)
                  <=> ! [X6,X7,X8] :
                        ( X4 = k3_mcart_1(X6,X7,X8)
                       => X5 = X8 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_mcart_1)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(l44_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ? [X4] :
            ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
            & ! [X5] :
                ( m1_subset_1(X5,X1)
               => ! [X6] :
                    ( m1_subset_1(X6,X2)
                   => ! [X7] :
                        ( m1_subset_1(X7,X3)
                       => X4 != k3_mcart_1(X5,X6,X7) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

fof(d6_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X2)
                 => ( X5 = k6_mcart_1(X1,X2,X3,X4)
                  <=> ! [X6,X7,X8] :
                        ( X4 = k3_mcart_1(X6,X7,X8)
                       => X5 = X7 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_mcart_1)).

fof(dt_k6_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(d5_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( X5 = k5_mcart_1(X1,X2,X3,X4)
                  <=> ! [X6,X7,X8] :
                        ( X4 = k3_mcart_1(X6,X7,X8)
                       => X5 = X6 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_mcart_1)).

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    inference(assume_negation,[status(cth)],[t48_mcart_1])).

fof(c_0_9,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37,X38] :
      ( ( X35 != k7_mcart_1(X31,X32,X33,X34)
        | X34 != k3_mcart_1(X36,X37,X38)
        | X35 = X38
        | ~ m1_subset_1(X35,X33)
        | ~ m1_subset_1(X34,k3_zfmisc_1(X31,X32,X33))
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0 )
      & ( X34 = k3_mcart_1(esk7_5(X31,X32,X33,X34,X35),esk8_5(X31,X32,X33,X34,X35),esk9_5(X31,X32,X33,X34,X35))
        | X35 = k7_mcart_1(X31,X32,X33,X34)
        | ~ m1_subset_1(X35,X33)
        | ~ m1_subset_1(X34,k3_zfmisc_1(X31,X32,X33))
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0 )
      & ( X35 != esk9_5(X31,X32,X33,X34,X35)
        | X35 = k7_mcart_1(X31,X32,X33,X34)
        | ~ m1_subset_1(X35,X33)
        | ~ m1_subset_1(X34,k3_zfmisc_1(X31,X32,X33))
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_mcart_1])])])])])).

fof(c_0_10,plain,(
    ! [X50,X51,X52,X53] :
      ( ~ m1_subset_1(X53,k3_zfmisc_1(X50,X51,X52))
      | m1_subset_1(k7_mcart_1(X50,X51,X52,X53),X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

fof(c_0_11,plain,(
    ! [X54,X55,X56,X57] :
      ( ( m1_subset_1(esk10_4(X54,X55,X56,X57),X54)
        | ~ m1_subset_1(X57,k3_zfmisc_1(X54,X55,X56))
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 )
      & ( m1_subset_1(esk11_4(X54,X55,X56,X57),X55)
        | ~ m1_subset_1(X57,k3_zfmisc_1(X54,X55,X56))
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 )
      & ( m1_subset_1(esk12_4(X54,X55,X56,X57),X56)
        | ~ m1_subset_1(X57,k3_zfmisc_1(X54,X55,X56))
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 )
      & ( X57 = k3_mcart_1(esk10_4(X54,X55,X56,X57),esk11_4(X54,X55,X56,X57),esk12_4(X54,X55,X56,X57))
        | ~ m1_subset_1(X57,k3_zfmisc_1(X54,X55,X56))
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).

fof(c_0_12,negated_conjecture,
    ( esk13_0 != k1_xboole_0
    & esk14_0 != k1_xboole_0
    & esk15_0 != k1_xboole_0
    & m1_subset_1(esk16_0,k3_zfmisc_1(esk13_0,esk14_0,esk15_0))
    & esk16_0 != k3_mcart_1(k5_mcart_1(esk13_0,esk14_0,esk15_0,esk16_0),k6_mcart_1(esk13_0,esk14_0,esk15_0,esk16_0),k7_mcart_1(esk13_0,esk14_0,esk15_0,esk16_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( X1 = X8
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 != k7_mcart_1(X2,X3,X4,X5)
    | X5 != k3_mcart_1(X6,X7,X8)
    | ~ m1_subset_1(X1,X4)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( X1 = k3_mcart_1(esk10_4(X2,X3,X4,X1),esk11_4(X2,X3,X4,X1),esk12_4(X2,X3,X4,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk16_0,k3_zfmisc_1(esk13_0,esk14_0,esk15_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk15_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( esk14_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( esk13_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k7_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X6
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])]),c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k3_mcart_1(esk10_4(esk13_0,esk14_0,esk15_0,esk16_0),esk11_4(esk13_0,esk14_0,esk15_0,esk16_0),esk12_4(esk13_0,esk14_0,esk15_0,esk16_0)) = esk16_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

fof(c_0_22,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( X24 != k6_mcart_1(X20,X21,X22,X23)
        | X23 != k3_mcart_1(X25,X26,X27)
        | X24 = X26
        | ~ m1_subset_1(X24,X21)
        | ~ m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( X23 = k3_mcart_1(esk4_5(X20,X21,X22,X23,X24),esk5_5(X20,X21,X22,X23,X24),esk6_5(X20,X21,X22,X23,X24))
        | X24 = k6_mcart_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X24,X21)
        | ~ m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( X24 != esk5_5(X20,X21,X22,X23,X24)
        | X24 = k6_mcart_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X24,X21)
        | ~ m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_mcart_1])])])])])])).

fof(c_0_23,plain,(
    ! [X46,X47,X48,X49] :
      ( ~ m1_subset_1(X49,k3_zfmisc_1(X46,X47,X48))
      | m1_subset_1(k6_mcart_1(X46,X47,X48,X49),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).

cnf(c_0_24,negated_conjecture,
    ( k7_mcart_1(X1,X2,X3,esk16_0) = esk12_4(esk13_0,esk14_0,esk15_0,esk16_0)
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk16_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( X1 = X7
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 != k6_mcart_1(X2,X3,X4,X5)
    | X5 != k3_mcart_1(X6,X7,X8)
    | ~ m1_subset_1(X1,X3)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( esk12_4(esk13_0,esk14_0,esk15_0,esk16_0) = k7_mcart_1(esk13_0,esk14_0,esk15_0,esk16_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_28,plain,
    ( k6_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X5
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( k3_mcart_1(esk10_4(esk13_0,esk14_0,esk15_0,esk16_0),esk11_4(esk13_0,esk14_0,esk15_0,esk16_0),k7_mcart_1(esk13_0,esk14_0,esk15_0,esk16_0)) = esk16_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_27])).

fof(c_0_30,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( X13 != k5_mcart_1(X9,X10,X11,X12)
        | X12 != k3_mcart_1(X14,X15,X16)
        | X13 = X14
        | ~ m1_subset_1(X13,X9)
        | ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X12 = k3_mcart_1(esk1_5(X9,X10,X11,X12,X13),esk2_5(X9,X10,X11,X12,X13),esk3_5(X9,X10,X11,X12,X13))
        | X13 = k5_mcart_1(X9,X10,X11,X12)
        | ~ m1_subset_1(X13,X9)
        | ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X13 != esk1_5(X9,X10,X11,X12,X13)
        | X13 = k5_mcart_1(X9,X10,X11,X12)
        | ~ m1_subset_1(X13,X9)
        | ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_mcart_1])])])])])])).

fof(c_0_31,plain,(
    ! [X42,X43,X44,X45] :
      ( ~ m1_subset_1(X45,k3_zfmisc_1(X42,X43,X44))
      | m1_subset_1(k5_mcart_1(X42,X43,X44,X45),X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

cnf(c_0_32,negated_conjecture,
    ( k6_mcart_1(X1,X2,X3,esk16_0) = esk11_4(esk13_0,esk14_0,esk15_0,esk16_0)
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk16_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( X1 = X6
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 != k5_mcart_1(X2,X3,X4,X5)
    | X5 != k3_mcart_1(X6,X7,X8)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( esk11_4(esk13_0,esk14_0,esk15_0,esk16_0) = k6_mcart_1(esk13_0,esk14_0,esk15_0,esk16_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_36,plain,
    ( k5_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X4
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( k3_mcart_1(esk10_4(esk13_0,esk14_0,esk15_0,esk16_0),k6_mcart_1(esk13_0,esk14_0,esk15_0,esk16_0),k7_mcart_1(esk13_0,esk14_0,esk15_0,esk16_0)) = esk16_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( k5_mcart_1(X1,X2,X3,esk16_0) = esk10_4(esk13_0,esk14_0,esk15_0,esk16_0)
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk16_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( esk10_4(esk13_0,esk14_0,esk15_0,esk16_0) = k5_mcart_1(esk13_0,esk14_0,esk15_0,esk16_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( esk16_0 != k3_mcart_1(k5_mcart_1(esk13_0,esk14_0,esk15_0,esk16_0),k6_mcart_1(esk13_0,esk14_0,esk15_0,esk16_0),k7_mcart_1(esk13_0,esk14_0,esk15_0,esk16_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_39]),c_0_40]),
    [proof]).

%------------------------------------------------------------------------------
