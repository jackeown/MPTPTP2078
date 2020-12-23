%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:52 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   38 (  93 expanded)
%              Number of clauses        :   23 (  33 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  200 ( 570 expanded)
%              Number of equality atoms :  141 ( 464 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_mcart_1)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(t47_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ? [X4] :
            ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
            & ? [X5,X6,X7] :
                ( X4 = k3_mcart_1(X5,X6,X7)
                & ~ ( k5_mcart_1(X1,X2,X3,X4) = X5
                    & k6_mcart_1(X1,X2,X3,X4) = X6
                    & k7_mcart_1(X1,X2,X3,X4) = X7 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_mcart_1)).

fof(dt_k6_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_mcart_1)).

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(c_0_7,plain,(
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

fof(c_0_8,plain,(
    ! [X50,X51,X52,X53] :
      ( ~ m1_subset_1(X53,k3_zfmisc_1(X50,X51,X52))
      | m1_subset_1(k7_mcart_1(X50,X51,X52,X53),X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ? [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
              & ? [X5,X6,X7] :
                  ( X4 = k3_mcart_1(X5,X6,X7)
                  & ~ ( k5_mcart_1(X1,X2,X3,X4) = X5
                      & k6_mcart_1(X1,X2,X3,X4) = X6
                      & k7_mcart_1(X1,X2,X3,X4) = X7 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t47_mcart_1])).

cnf(c_0_10,plain,
    ( X1 = X8
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 != k7_mcart_1(X2,X3,X4,X5)
    | X5 != k3_mcart_1(X6,X7,X8)
    | ~ m1_subset_1(X1,X4)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( esk10_0 != k1_xboole_0
    & esk11_0 != k1_xboole_0
    & esk12_0 != k1_xboole_0
    & m1_subset_1(esk13_0,k3_zfmisc_1(esk10_0,esk11_0,esk12_0))
    & esk13_0 = k3_mcart_1(esk14_0,esk15_0,esk16_0)
    & ( k5_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0) != esk14_0
      | k6_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0) != esk15_0
      | k7_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0) != esk16_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
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

fof(c_0_14,plain,(
    ! [X46,X47,X48,X49] :
      ( ~ m1_subset_1(X49,k3_zfmisc_1(X46,X47,X48))
      | m1_subset_1(k6_mcart_1(X46,X47,X48,X49),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).

cnf(c_0_15,plain,
    ( k7_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X6
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])]),c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( esk13_0 = k3_mcart_1(esk14_0,esk15_0,esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( X1 = X7
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 != k6_mcart_1(X2,X3,X4,X5)
    | X5 != k3_mcart_1(X6,X7,X8)
    | ~ m1_subset_1(X1,X3)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
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

fof(c_0_20,plain,(
    ! [X42,X43,X44,X45] :
      ( ~ m1_subset_1(X45,k3_zfmisc_1(X42,X43,X44))
      | m1_subset_1(k5_mcart_1(X42,X43,X44,X45),X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

cnf(c_0_21,negated_conjecture,
    ( k7_mcart_1(X1,X2,X3,esk13_0) = esk16_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk13_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk13_0,k3_zfmisc_1(esk10_0,esk11_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( esk12_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( esk11_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( esk10_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( k6_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X5
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])]),c_0_18])).

cnf(c_0_27,plain,
    ( X1 = X6
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 != k5_mcart_1(X2,X3,X4,X5)
    | X5 != k3_mcart_1(X6,X7,X8)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( k5_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0) != esk14_0
    | k6_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0) != esk15_0
    | k7_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0) != esk16_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( k7_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0) = esk16_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k6_mcart_1(X1,X2,X3,esk13_0) = esk15_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk13_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_32,plain,
    ( k5_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X4
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k5_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0) != esk14_0
    | k6_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0) != esk15_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_34,negated_conjecture,
    ( k6_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0) = esk15_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( k5_mcart_1(X1,X2,X3,esk13_0) = esk14_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk13_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( k5_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0) != esk14_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_36]),c_0_23]),c_0_24]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d7_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>![X5]:(m1_subset_1(X5,X3)=>(X5=k7_mcart_1(X1,X2,X3,X4)<=>![X6, X7, X8]:(X4=k3_mcart_1(X6,X7,X8)=>X5=X8))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_mcart_1)).
% 0.13/0.38  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 0.13/0.38  fof(t47_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&?[X5, X6, X7]:(X4=k3_mcart_1(X5,X6,X7)&~(((k5_mcart_1(X1,X2,X3,X4)=X5&k6_mcart_1(X1,X2,X3,X4)=X6)&k7_mcart_1(X1,X2,X3,X4)=X7)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_mcart_1)).
% 0.13/0.38  fof(d6_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>![X5]:(m1_subset_1(X5,X2)=>(X5=k6_mcart_1(X1,X2,X3,X4)<=>![X6, X7, X8]:(X4=k3_mcart_1(X6,X7,X8)=>X5=X7))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_mcart_1)).
% 0.13/0.38  fof(dt_k6_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 0.13/0.38  fof(d5_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>![X5]:(m1_subset_1(X5,X1)=>(X5=k5_mcart_1(X1,X2,X3,X4)<=>![X6, X7, X8]:(X4=k3_mcart_1(X6,X7,X8)=>X5=X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_mcart_1)).
% 0.13/0.38  fof(dt_k5_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 0.13/0.38  fof(c_0_7, plain, ![X31, X32, X33, X34, X35, X36, X37, X38]:((X35!=k7_mcart_1(X31,X32,X33,X34)|(X34!=k3_mcart_1(X36,X37,X38)|X35=X38)|~m1_subset_1(X35,X33)|~m1_subset_1(X34,k3_zfmisc_1(X31,X32,X33))|(X31=k1_xboole_0|X32=k1_xboole_0|X33=k1_xboole_0))&((X34=k3_mcart_1(esk7_5(X31,X32,X33,X34,X35),esk8_5(X31,X32,X33,X34,X35),esk9_5(X31,X32,X33,X34,X35))|X35=k7_mcart_1(X31,X32,X33,X34)|~m1_subset_1(X35,X33)|~m1_subset_1(X34,k3_zfmisc_1(X31,X32,X33))|(X31=k1_xboole_0|X32=k1_xboole_0|X33=k1_xboole_0))&(X35!=esk9_5(X31,X32,X33,X34,X35)|X35=k7_mcart_1(X31,X32,X33,X34)|~m1_subset_1(X35,X33)|~m1_subset_1(X34,k3_zfmisc_1(X31,X32,X33))|(X31=k1_xboole_0|X32=k1_xboole_0|X33=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_mcart_1])])])])])).
% 0.13/0.38  fof(c_0_8, plain, ![X50, X51, X52, X53]:(~m1_subset_1(X53,k3_zfmisc_1(X50,X51,X52))|m1_subset_1(k7_mcart_1(X50,X51,X52,X53),X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&?[X5, X6, X7]:(X4=k3_mcart_1(X5,X6,X7)&~(((k5_mcart_1(X1,X2,X3,X4)=X5&k6_mcart_1(X1,X2,X3,X4)=X6)&k7_mcart_1(X1,X2,X3,X4)=X7))))))), inference(assume_negation,[status(cth)],[t47_mcart_1])).
% 0.13/0.38  cnf(c_0_10, plain, (X1=X8|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X1!=k7_mcart_1(X2,X3,X4,X5)|X5!=k3_mcart_1(X6,X7,X8)|~m1_subset_1(X1,X4)|~m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_11, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, (((esk10_0!=k1_xboole_0&esk11_0!=k1_xboole_0)&esk12_0!=k1_xboole_0)&(m1_subset_1(esk13_0,k3_zfmisc_1(esk10_0,esk11_0,esk12_0))&(esk13_0=k3_mcart_1(esk14_0,esk15_0,esk16_0)&(k5_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0)!=esk14_0|k6_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0)!=esk15_0|k7_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0)!=esk16_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:((X24!=k6_mcart_1(X20,X21,X22,X23)|(X23!=k3_mcart_1(X25,X26,X27)|X24=X26)|~m1_subset_1(X24,X21)|~m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))|(X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&((X23=k3_mcart_1(esk4_5(X20,X21,X22,X23,X24),esk5_5(X20,X21,X22,X23,X24),esk6_5(X20,X21,X22,X23,X24))|X24=k6_mcart_1(X20,X21,X22,X23)|~m1_subset_1(X24,X21)|~m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))|(X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&(X24!=esk5_5(X20,X21,X22,X23,X24)|X24=k6_mcart_1(X20,X21,X22,X23)|~m1_subset_1(X24,X21)|~m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))|(X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_mcart_1])])])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X46, X47, X48, X49]:(~m1_subset_1(X49,k3_zfmisc_1(X46,X47,X48))|m1_subset_1(k6_mcart_1(X46,X47,X48,X49),X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).
% 0.13/0.38  cnf(c_0_15, plain, (k7_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6))=X6|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])]), c_0_11])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (esk13_0=k3_mcart_1(esk14_0,esk15_0,esk16_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_17, plain, (X1=X7|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X1!=k6_mcart_1(X2,X3,X4,X5)|X5!=k3_mcart_1(X6,X7,X8)|~m1_subset_1(X1,X3)|~m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_18, plain, (m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_19, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((X13!=k5_mcart_1(X9,X10,X11,X12)|(X12!=k3_mcart_1(X14,X15,X16)|X13=X14)|~m1_subset_1(X13,X9)|~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|(X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0))&((X12=k3_mcart_1(esk1_5(X9,X10,X11,X12,X13),esk2_5(X9,X10,X11,X12,X13),esk3_5(X9,X10,X11,X12,X13))|X13=k5_mcart_1(X9,X10,X11,X12)|~m1_subset_1(X13,X9)|~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|(X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0))&(X13!=esk1_5(X9,X10,X11,X12,X13)|X13=k5_mcart_1(X9,X10,X11,X12)|~m1_subset_1(X13,X9)|~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|(X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_mcart_1])])])])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X42, X43, X44, X45]:(~m1_subset_1(X45,k3_zfmisc_1(X42,X43,X44))|m1_subset_1(k5_mcart_1(X42,X43,X44,X45),X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (k7_mcart_1(X1,X2,X3,esk13_0)=esk16_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk13_0,k3_zfmisc_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk13_0,k3_zfmisc_1(esk10_0,esk11_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (esk12_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (esk11_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (esk10_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_26, plain, (k6_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6))=X5|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])]), c_0_18])).
% 0.13/0.38  cnf(c_0_27, plain, (X1=X6|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X1!=k5_mcart_1(X2,X3,X4,X5)|X5!=k3_mcart_1(X6,X7,X8)|~m1_subset_1(X1,X2)|~m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_28, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (k5_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0)!=esk14_0|k6_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0)!=esk15_0|k7_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0)!=esk16_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (k7_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0)=esk16_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (k6_mcart_1(X1,X2,X3,esk13_0)=esk15_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk13_0,k3_zfmisc_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_26, c_0_16])).
% 0.13/0.38  cnf(c_0_32, plain, (k5_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6))=X4|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])]), c_0_28])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (k5_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0)!=esk14_0|k6_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0)!=esk15_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (k6_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0)=esk15_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (k5_mcart_1(X1,X2,X3,esk13_0)=esk14_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk13_0,k3_zfmisc_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_32, c_0_16])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k5_mcart_1(esk10_0,esk11_0,esk12_0,esk13_0)!=esk14_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_22]), c_0_36]), c_0_23]), c_0_24]), c_0_25]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 38
% 0.13/0.38  # Proof object clause steps            : 23
% 0.13/0.38  # Proof object formula steps           : 15
% 0.13/0.38  # Proof object conjectures             : 17
% 0.13/0.38  # Proof object clause conjectures      : 14
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 7
% 0.13/0.38  # Proof object generating inferences   : 6
% 0.13/0.38  # Proof object simplifying inferences  : 23
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 7
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 18
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 18
% 0.13/0.38  # Processed clauses                    : 57
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 57
% 0.13/0.38  # Other redundant clauses eliminated   : 6
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 4
% 0.13/0.38  # Generated clauses                    : 50
% 0.13/0.38  # ...of the previous two non-trivial   : 53
% 0.13/0.38  # Contextual simplify-reflections      : 3
% 0.13/0.38  # Paramodulations                      : 47
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 6
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 32
% 0.13/0.38  #    Positive orientable unit clauses  : 6
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 22
% 0.13/0.38  # Current number of unprocessed clauses: 32
% 0.13/0.38  # ...number of literals in the above   : 168
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 22
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 43
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 22
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.38  # Unit Clause-clause subsumption calls : 1
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3451
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
