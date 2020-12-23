%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0900+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:22 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 838 expanded)
%              Number of clauses        :   32 ( 278 expanded)
%              Number of leaves         :   10 ( 202 expanded)
%              Depth                    :   16
%              Number of atoms          :  323 (4661 expanded)
%              Number of equality atoms :  231 (3651 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(d11_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => ! [X6] :
                  ( m1_subset_1(X6,X4)
                 => ( X6 = k11_mcart_1(X1,X2,X3,X4,X5)
                  <=> ! [X7,X8,X9,X10] :
                        ( X5 = k4_mcart_1(X7,X8,X9,X10)
                       => X6 = X10 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_mcart_1)).

fof(dt_k11_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(l68_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ? [X5] :
            ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ! [X8] :
                        ( m1_subset_1(X8,X3)
                       => ! [X9] :
                            ( m1_subset_1(X9,X4)
                           => X5 != k4_mcart_1(X6,X7,X8,X9) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

fof(d10_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => ! [X6] :
                  ( m1_subset_1(X6,X3)
                 => ( X6 = k10_mcart_1(X1,X2,X3,X4,X5)
                  <=> ! [X7,X8,X9,X10] :
                        ( X5 = k4_mcart_1(X7,X8,X9,X10)
                       => X6 = X9 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_mcart_1)).

fof(dt_k10_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(d9_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( X6 = k9_mcart_1(X1,X2,X3,X4,X5)
                  <=> ! [X7,X8,X9,X10] :
                        ( X5 = k4_mcart_1(X7,X8,X9,X10)
                       => X6 = X8 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_mcart_1)).

fof(dt_k9_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(d8_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ( X6 = k8_mcart_1(X1,X2,X3,X4,X5)
                  <=> ! [X7,X8,X9,X10] :
                        ( X5 = k4_mcart_1(X7,X8,X9,X10)
                       => X6 = X7 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_mcart_1)).

fof(dt_k8_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & X4 != k1_xboole_0
          & ~ ! [X5] :
                ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
               => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    inference(assume_negation,[status(cth)],[t60_mcart_1])).

fof(c_0_11,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( X30 != k11_mcart_1(X25,X26,X27,X28,X29)
        | X29 != k4_mcart_1(X31,X32,X33,X34)
        | X30 = X34
        | ~ m1_subset_1(X30,X28)
        | ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( X29 = k4_mcart_1(esk5_6(X25,X26,X27,X28,X29,X30),esk6_6(X25,X26,X27,X28,X29,X30),esk7_6(X25,X26,X27,X28,X29,X30),esk8_6(X25,X26,X27,X28,X29,X30))
        | X30 = k11_mcart_1(X25,X26,X27,X28,X29)
        | ~ m1_subset_1(X30,X28)
        | ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( X30 != esk8_6(X25,X26,X27,X28,X29,X30)
        | X30 = k11_mcart_1(X25,X26,X27,X28,X29)
        | ~ m1_subset_1(X30,X28)
        | ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_mcart_1])])])])])).

fof(c_0_12,plain,(
    ! [X72,X73,X74,X75,X76] :
      ( ~ m1_subset_1(X76,k4_zfmisc_1(X72,X73,X74,X75))
      | m1_subset_1(k11_mcart_1(X72,X73,X74,X75,X76),X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).

fof(c_0_13,plain,(
    ! [X87,X88,X89,X90,X91] :
      ( ( m1_subset_1(esk17_5(X87,X88,X89,X90,X91),X87)
        | ~ m1_subset_1(X91,k4_zfmisc_1(X87,X88,X89,X90))
        | X87 = k1_xboole_0
        | X88 = k1_xboole_0
        | X89 = k1_xboole_0
        | X90 = k1_xboole_0 )
      & ( m1_subset_1(esk18_5(X87,X88,X89,X90,X91),X88)
        | ~ m1_subset_1(X91,k4_zfmisc_1(X87,X88,X89,X90))
        | X87 = k1_xboole_0
        | X88 = k1_xboole_0
        | X89 = k1_xboole_0
        | X90 = k1_xboole_0 )
      & ( m1_subset_1(esk19_5(X87,X88,X89,X90,X91),X89)
        | ~ m1_subset_1(X91,k4_zfmisc_1(X87,X88,X89,X90))
        | X87 = k1_xboole_0
        | X88 = k1_xboole_0
        | X89 = k1_xboole_0
        | X90 = k1_xboole_0 )
      & ( m1_subset_1(esk20_5(X87,X88,X89,X90,X91),X90)
        | ~ m1_subset_1(X91,k4_zfmisc_1(X87,X88,X89,X90))
        | X87 = k1_xboole_0
        | X88 = k1_xboole_0
        | X89 = k1_xboole_0
        | X90 = k1_xboole_0 )
      & ( X91 = k4_mcart_1(esk17_5(X87,X88,X89,X90,X91),esk18_5(X87,X88,X89,X90,X91),esk19_5(X87,X88,X89,X90,X91),esk20_5(X87,X88,X89,X90,X91))
        | ~ m1_subset_1(X91,k4_zfmisc_1(X87,X88,X89,X90))
        | X87 = k1_xboole_0
        | X88 = k1_xboole_0
        | X89 = k1_xboole_0
        | X90 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).

fof(c_0_14,negated_conjecture,
    ( esk21_0 != k1_xboole_0
    & esk22_0 != k1_xboole_0
    & esk23_0 != k1_xboole_0
    & esk24_0 != k1_xboole_0
    & m1_subset_1(esk25_0,k4_zfmisc_1(esk21_0,esk22_0,esk23_0,esk24_0))
    & esk25_0 != k4_mcart_1(k8_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),k9_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),k10_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),k11_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( X1 = X10
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 != k11_mcart_1(X2,X3,X4,X5,X6)
    | X6 != k4_mcart_1(X7,X8,X9,X10)
    | ~ m1_subset_1(X1,X5)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( X1 = k4_mcart_1(esk17_5(X2,X3,X4,X5,X1),esk18_5(X2,X3,X4,X5,X1),esk19_5(X2,X3,X4,X5,X1),esk20_5(X2,X3,X4,X5,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk25_0,k4_zfmisc_1(esk21_0,esk22_0,esk23_0,esk24_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( esk24_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( esk23_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( esk22_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( esk21_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k11_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X8
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_15])]),c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k4_mcart_1(esk17_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),esk18_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),esk19_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),esk20_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0)) = esk25_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])).

fof(c_0_25,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( X16 != k10_mcart_1(X11,X12,X13,X14,X15)
        | X15 != k4_mcart_1(X17,X18,X19,X20)
        | X16 = X19
        | ~ m1_subset_1(X16,X13)
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X15 = k4_mcart_1(esk1_6(X11,X12,X13,X14,X15,X16),esk2_6(X11,X12,X13,X14,X15,X16),esk3_6(X11,X12,X13,X14,X15,X16),esk4_6(X11,X12,X13,X14,X15,X16))
        | X16 = k10_mcart_1(X11,X12,X13,X14,X15)
        | ~ m1_subset_1(X16,X13)
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X16 != esk3_6(X11,X12,X13,X14,X15,X16)
        | X16 = k10_mcart_1(X11,X12,X13,X14,X15)
        | ~ m1_subset_1(X16,X13)
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_mcart_1])])])])])])).

fof(c_0_26,plain,(
    ! [X67,X68,X69,X70,X71] :
      ( ~ m1_subset_1(X71,k4_zfmisc_1(X67,X68,X69,X70))
      | m1_subset_1(k10_mcart_1(X67,X68,X69,X70,X71),X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).

cnf(c_0_27,negated_conjecture,
    ( k11_mcart_1(X1,X2,X3,X4,esk25_0) = esk20_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk25_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( X1 = X9
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 != k10_mcart_1(X2,X3,X4,X5,X6)
    | X6 != k4_mcart_1(X7,X8,X9,X10)
    | ~ m1_subset_1(X1,X4)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( esk20_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0) = k11_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_31,plain,
    ( k10_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X7
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])]),c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( k4_mcart_1(esk17_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),esk18_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),esk19_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),k11_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0)) = esk25_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_30])).

fof(c_0_33,plain,(
    ! [X53,X54,X55,X56,X57,X58,X59,X60,X61,X62] :
      ( ( X58 != k9_mcart_1(X53,X54,X55,X56,X57)
        | X57 != k4_mcart_1(X59,X60,X61,X62)
        | X58 = X60
        | ~ m1_subset_1(X58,X54)
        | ~ m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 )
      & ( X57 = k4_mcart_1(esk13_6(X53,X54,X55,X56,X57,X58),esk14_6(X53,X54,X55,X56,X57,X58),esk15_6(X53,X54,X55,X56,X57,X58),esk16_6(X53,X54,X55,X56,X57,X58))
        | X58 = k9_mcart_1(X53,X54,X55,X56,X57)
        | ~ m1_subset_1(X58,X54)
        | ~ m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 )
      & ( X58 != esk14_6(X53,X54,X55,X56,X57,X58)
        | X58 = k9_mcart_1(X53,X54,X55,X56,X57)
        | ~ m1_subset_1(X58,X54)
        | ~ m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_mcart_1])])])])])])).

fof(c_0_34,plain,(
    ! [X82,X83,X84,X85,X86] :
      ( ~ m1_subset_1(X86,k4_zfmisc_1(X82,X83,X84,X85))
      | m1_subset_1(k9_mcart_1(X82,X83,X84,X85,X86),X83) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

cnf(c_0_35,negated_conjecture,
    ( k10_mcart_1(X1,X2,X3,X4,esk25_0) = esk19_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk25_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( X1 = X8
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 != k9_mcart_1(X2,X3,X4,X5,X6)
    | X6 != k4_mcart_1(X7,X8,X9,X10)
    | ~ m1_subset_1(X1,X3)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( esk19_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0) = k10_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_39,plain,
    ( k9_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X6
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])]),c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( k4_mcart_1(esk17_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),esk18_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),k10_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),k11_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0)) = esk25_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_38])).

fof(c_0_41,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45,X46,X47,X48] :
      ( ( X44 != k8_mcart_1(X39,X40,X41,X42,X43)
        | X43 != k4_mcart_1(X45,X46,X47,X48)
        | X44 = X45
        | ~ m1_subset_1(X44,X39)
        | ~ m1_subset_1(X43,k4_zfmisc_1(X39,X40,X41,X42))
        | X39 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0 )
      & ( X43 = k4_mcart_1(esk9_6(X39,X40,X41,X42,X43,X44),esk10_6(X39,X40,X41,X42,X43,X44),esk11_6(X39,X40,X41,X42,X43,X44),esk12_6(X39,X40,X41,X42,X43,X44))
        | X44 = k8_mcart_1(X39,X40,X41,X42,X43)
        | ~ m1_subset_1(X44,X39)
        | ~ m1_subset_1(X43,k4_zfmisc_1(X39,X40,X41,X42))
        | X39 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0 )
      & ( X44 != esk9_6(X39,X40,X41,X42,X43,X44)
        | X44 = k8_mcart_1(X39,X40,X41,X42,X43)
        | ~ m1_subset_1(X44,X39)
        | ~ m1_subset_1(X43,k4_zfmisc_1(X39,X40,X41,X42))
        | X39 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_mcart_1])])])])])])).

fof(c_0_42,plain,(
    ! [X77,X78,X79,X80,X81] :
      ( ~ m1_subset_1(X81,k4_zfmisc_1(X77,X78,X79,X80))
      | m1_subset_1(k8_mcart_1(X77,X78,X79,X80,X81),X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

cnf(c_0_43,negated_conjecture,
    ( k9_mcart_1(X1,X2,X3,X4,esk25_0) = esk18_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk25_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( X1 = X7
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 != k8_mcart_1(X2,X3,X4,X5,X6)
    | X6 != k4_mcart_1(X7,X8,X9,X10)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( esk18_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0) = k9_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_47,plain,
    ( k8_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X5
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])]),c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( k4_mcart_1(esk17_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),k9_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),k10_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),k11_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0)) = esk25_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( k8_mcart_1(X1,X2,X3,X4,esk25_0) = esk17_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk25_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( esk17_5(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0) = k8_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( esk25_0 != k4_mcart_1(k8_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),k9_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),k10_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0),k11_mcart_1(esk21_0,esk22_0,esk23_0,esk24_0,esk25_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_50]),c_0_51]),
    [proof]).

%------------------------------------------------------------------------------
