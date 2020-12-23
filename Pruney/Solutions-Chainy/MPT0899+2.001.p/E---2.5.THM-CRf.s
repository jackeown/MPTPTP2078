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
% DateTime   : Thu Dec  3 11:00:03 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 139 expanded)
%              Number of clauses        :   30 (  48 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  294 (1032 expanded)
%              Number of equality atoms :  217 ( 880 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal clause size      :   25 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t59_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ? [X5] :
            ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
            & ? [X6,X7,X8,X9] :
                ( X5 = k4_mcart_1(X6,X7,X8,X9)
                & ~ ( k8_mcart_1(X1,X2,X3,X4,X5) = X6
                    & k9_mcart_1(X1,X2,X3,X4,X5) = X7
                    & k10_mcart_1(X1,X2,X3,X4,X5) = X8
                    & k11_mcart_1(X1,X2,X3,X4,X5) = X9 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).

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

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X72,X73,X74,X75,X76] :
      ( ~ m1_subset_1(X76,k4_zfmisc_1(X72,X73,X74,X75))
      | m1_subset_1(k11_mcart_1(X72,X73,X74,X75,X76),X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & X4 != k1_xboole_0
          & ? [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
              & ? [X6,X7,X8,X9] :
                  ( X5 = k4_mcart_1(X6,X7,X8,X9)
                  & ~ ( k8_mcart_1(X1,X2,X3,X4,X5) = X6
                      & k9_mcart_1(X1,X2,X3,X4,X5) = X7
                      & k10_mcart_1(X1,X2,X3,X4,X5) = X8
                      & k11_mcart_1(X1,X2,X3,X4,X5) = X9 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_mcart_1])).

cnf(c_0_12,plain,
    ( X1 = X10
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 != k11_mcart_1(X2,X3,X4,X5,X6)
    | X6 != k4_mcart_1(X7,X8,X9,X10)
    | ~ m1_subset_1(X1,X5)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( esk17_0 != k1_xboole_0
    & esk18_0 != k1_xboole_0
    & esk19_0 != k1_xboole_0
    & esk20_0 != k1_xboole_0
    & m1_subset_1(esk21_0,k4_zfmisc_1(esk17_0,esk18_0,esk19_0,esk20_0))
    & esk21_0 = k4_mcart_1(esk22_0,esk23_0,esk24_0,esk25_0)
    & ( k8_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk22_0
      | k9_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk23_0
      | k10_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk24_0
      | k11_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk25_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
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

fof(c_0_16,plain,(
    ! [X67,X68,X69,X70,X71] :
      ( ~ m1_subset_1(X71,k4_zfmisc_1(X67,X68,X69,X70))
      | m1_subset_1(k10_mcart_1(X67,X68,X69,X70,X71),X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).

cnf(c_0_17,plain,
    ( k11_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X8
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])]),c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( esk21_0 = k4_mcart_1(esk22_0,esk23_0,esk24_0,esk25_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( X1 = X9
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 != k10_mcart_1(X2,X3,X4,X5,X6)
    | X6 != k4_mcart_1(X7,X8,X9,X10)
    | ~ m1_subset_1(X1,X4)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
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

fof(c_0_22,plain,(
    ! [X82,X83,X84,X85,X86] :
      ( ~ m1_subset_1(X86,k4_zfmisc_1(X82,X83,X84,X85))
      | m1_subset_1(k9_mcart_1(X82,X83,X84,X85,X86),X83) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

cnf(c_0_23,negated_conjecture,
    ( k11_mcart_1(X1,X2,X3,X4,esk21_0) = esk25_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk21_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk21_0,k4_zfmisc_1(esk17_0,esk18_0,esk19_0,esk20_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( esk20_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( esk19_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( esk18_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( esk17_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( k10_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X7
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])]),c_0_20])).

cnf(c_0_30,plain,
    ( X1 = X8
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 != k9_mcart_1(X2,X3,X4,X5,X6)
    | X6 != k4_mcart_1(X7,X8,X9,X10)
    | ~ m1_subset_1(X1,X3)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
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

fof(c_0_33,plain,(
    ! [X77,X78,X79,X80,X81] :
      ( ~ m1_subset_1(X81,k4_zfmisc_1(X77,X78,X79,X80))
      | m1_subset_1(k8_mcart_1(X77,X78,X79,X80,X81),X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

cnf(c_0_34,negated_conjecture,
    ( k8_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk22_0
    | k9_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk23_0
    | k10_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk24_0
    | k11_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk25_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( k11_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) = esk25_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k10_mcart_1(X1,X2,X3,X4,esk21_0) = esk24_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk21_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_37,plain,
    ( k9_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X6
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])]),c_0_31])).

cnf(c_0_38,plain,
    ( X1 = X7
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 != k8_mcart_1(X2,X3,X4,X5,X6)
    | X6 != k4_mcart_1(X7,X8,X9,X10)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k10_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk24_0
    | k8_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk22_0
    | k9_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk23_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_41,negated_conjecture,
    ( k10_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) = esk24_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( k9_mcart_1(X1,X2,X3,X4,esk21_0) = esk23_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk21_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_18])).

cnf(c_0_43,plain,
    ( k8_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8)) = X5
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])]),c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k8_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk22_0
    | k9_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk23_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( k9_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) = esk23_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( k8_mcart_1(X1,X2,X3,X4,esk21_0) = esk22_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk21_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( k8_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0) != esk22_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_24]),c_0_47]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:26:30 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.029 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(d11_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>![X6]:(m1_subset_1(X6,X4)=>(X6=k11_mcart_1(X1,X2,X3,X4,X5)<=>![X7, X8, X9, X10]:(X5=k4_mcart_1(X7,X8,X9,X10)=>X6=X10))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_mcart_1)).
% 0.21/0.39  fof(dt_k11_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_mcart_1)).
% 0.21/0.39  fof(t59_mcart_1, conjecture, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_mcart_1)).
% 0.21/0.39  fof(d10_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>![X6]:(m1_subset_1(X6,X3)=>(X6=k10_mcart_1(X1,X2,X3,X4,X5)<=>![X7, X8, X9, X10]:(X5=k4_mcart_1(X7,X8,X9,X10)=>X6=X9))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_mcart_1)).
% 0.21/0.39  fof(dt_k10_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_mcart_1)).
% 0.21/0.39  fof(d9_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>![X6]:(m1_subset_1(X6,X2)=>(X6=k9_mcart_1(X1,X2,X3,X4,X5)<=>![X7, X8, X9, X10]:(X5=k4_mcart_1(X7,X8,X9,X10)=>X6=X8))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_mcart_1)).
% 0.21/0.39  fof(dt_k9_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 0.21/0.39  fof(d8_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>![X6]:(m1_subset_1(X6,X1)=>(X6=k8_mcart_1(X1,X2,X3,X4,X5)<=>![X7, X8, X9, X10]:(X5=k4_mcart_1(X7,X8,X9,X10)=>X6=X7))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_mcart_1)).
% 0.21/0.39  fof(dt_k8_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_mcart_1)).
% 0.21/0.39  fof(c_0_9, plain, ![X25, X26, X27, X28, X29, X30, X31, X32, X33, X34]:((X30!=k11_mcart_1(X25,X26,X27,X28,X29)|(X29!=k4_mcart_1(X31,X32,X33,X34)|X30=X34)|~m1_subset_1(X30,X28)|~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0))&((X29=k4_mcart_1(esk5_6(X25,X26,X27,X28,X29,X30),esk6_6(X25,X26,X27,X28,X29,X30),esk7_6(X25,X26,X27,X28,X29,X30),esk8_6(X25,X26,X27,X28,X29,X30))|X30=k11_mcart_1(X25,X26,X27,X28,X29)|~m1_subset_1(X30,X28)|~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0))&(X30!=esk8_6(X25,X26,X27,X28,X29,X30)|X30=k11_mcart_1(X25,X26,X27,X28,X29)|~m1_subset_1(X30,X28)|~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_mcart_1])])])])])).
% 0.21/0.39  fof(c_0_10, plain, ![X72, X73, X74, X75, X76]:(~m1_subset_1(X76,k4_zfmisc_1(X72,X73,X74,X75))|m1_subset_1(k11_mcart_1(X72,X73,X74,X75,X76),X75)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).
% 0.21/0.39  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))&?[X6, X7, X8, X9]:(X5=k4_mcart_1(X6,X7,X8,X9)&~((((k8_mcart_1(X1,X2,X3,X4,X5)=X6&k9_mcart_1(X1,X2,X3,X4,X5)=X7)&k10_mcart_1(X1,X2,X3,X4,X5)=X8)&k11_mcart_1(X1,X2,X3,X4,X5)=X9))))))), inference(assume_negation,[status(cth)],[t59_mcart_1])).
% 0.21/0.39  cnf(c_0_12, plain, (X1=X10|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|X1!=k11_mcart_1(X2,X3,X4,X5,X6)|X6!=k4_mcart_1(X7,X8,X9,X10)|~m1_subset_1(X1,X5)|~m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_13, plain, (m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  fof(c_0_14, negated_conjecture, ((((esk17_0!=k1_xboole_0&esk18_0!=k1_xboole_0)&esk19_0!=k1_xboole_0)&esk20_0!=k1_xboole_0)&(m1_subset_1(esk21_0,k4_zfmisc_1(esk17_0,esk18_0,esk19_0,esk20_0))&(esk21_0=k4_mcart_1(esk22_0,esk23_0,esk24_0,esk25_0)&(k8_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk22_0|k9_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk23_0|k10_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk24_0|k11_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk25_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.21/0.39  fof(c_0_15, plain, ![X11, X12, X13, X14, X15, X16, X17, X18, X19, X20]:((X16!=k10_mcart_1(X11,X12,X13,X14,X15)|(X15!=k4_mcart_1(X17,X18,X19,X20)|X16=X19)|~m1_subset_1(X16,X13)|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&((X15=k4_mcart_1(esk1_6(X11,X12,X13,X14,X15,X16),esk2_6(X11,X12,X13,X14,X15,X16),esk3_6(X11,X12,X13,X14,X15,X16),esk4_6(X11,X12,X13,X14,X15,X16))|X16=k10_mcart_1(X11,X12,X13,X14,X15)|~m1_subset_1(X16,X13)|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&(X16!=esk3_6(X11,X12,X13,X14,X15,X16)|X16=k10_mcart_1(X11,X12,X13,X14,X15)|~m1_subset_1(X16,X13)|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_mcart_1])])])])])])).
% 0.21/0.39  fof(c_0_16, plain, ![X67, X68, X69, X70, X71]:(~m1_subset_1(X71,k4_zfmisc_1(X67,X68,X69,X70))|m1_subset_1(k10_mcart_1(X67,X68,X69,X70,X71),X69)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).
% 0.21/0.39  cnf(c_0_17, plain, (k11_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8))=X8|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])]), c_0_13])).
% 0.21/0.39  cnf(c_0_18, negated_conjecture, (esk21_0=k4_mcart_1(esk22_0,esk23_0,esk24_0,esk25_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_19, plain, (X1=X9|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|X1!=k10_mcart_1(X2,X3,X4,X5,X6)|X6!=k4_mcart_1(X7,X8,X9,X10)|~m1_subset_1(X1,X4)|~m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_20, plain, (m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  fof(c_0_21, plain, ![X53, X54, X55, X56, X57, X58, X59, X60, X61, X62]:((X58!=k9_mcart_1(X53,X54,X55,X56,X57)|(X57!=k4_mcart_1(X59,X60,X61,X62)|X58=X60)|~m1_subset_1(X58,X54)|~m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))|(X53=k1_xboole_0|X54=k1_xboole_0|X55=k1_xboole_0|X56=k1_xboole_0))&((X57=k4_mcart_1(esk13_6(X53,X54,X55,X56,X57,X58),esk14_6(X53,X54,X55,X56,X57,X58),esk15_6(X53,X54,X55,X56,X57,X58),esk16_6(X53,X54,X55,X56,X57,X58))|X58=k9_mcart_1(X53,X54,X55,X56,X57)|~m1_subset_1(X58,X54)|~m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))|(X53=k1_xboole_0|X54=k1_xboole_0|X55=k1_xboole_0|X56=k1_xboole_0))&(X58!=esk14_6(X53,X54,X55,X56,X57,X58)|X58=k9_mcart_1(X53,X54,X55,X56,X57)|~m1_subset_1(X58,X54)|~m1_subset_1(X57,k4_zfmisc_1(X53,X54,X55,X56))|(X53=k1_xboole_0|X54=k1_xboole_0|X55=k1_xboole_0|X56=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_mcart_1])])])])])])).
% 0.21/0.39  fof(c_0_22, plain, ![X82, X83, X84, X85, X86]:(~m1_subset_1(X86,k4_zfmisc_1(X82,X83,X84,X85))|m1_subset_1(k9_mcart_1(X82,X83,X84,X85,X86),X83)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).
% 0.21/0.39  cnf(c_0_23, negated_conjecture, (k11_mcart_1(X1,X2,X3,X4,esk21_0)=esk25_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk21_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk21_0,k4_zfmisc_1(esk17_0,esk18_0,esk19_0,esk20_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (esk20_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_26, negated_conjecture, (esk19_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (esk18_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (esk17_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_29, plain, (k10_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8))=X7|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])]), c_0_20])).
% 0.21/0.39  cnf(c_0_30, plain, (X1=X8|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|X1!=k9_mcart_1(X2,X3,X4,X5,X6)|X6!=k4_mcart_1(X7,X8,X9,X10)|~m1_subset_1(X1,X3)|~m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_31, plain, (m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  fof(c_0_32, plain, ![X39, X40, X41, X42, X43, X44, X45, X46, X47, X48]:((X44!=k8_mcart_1(X39,X40,X41,X42,X43)|(X43!=k4_mcart_1(X45,X46,X47,X48)|X44=X45)|~m1_subset_1(X44,X39)|~m1_subset_1(X43,k4_zfmisc_1(X39,X40,X41,X42))|(X39=k1_xboole_0|X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0))&((X43=k4_mcart_1(esk9_6(X39,X40,X41,X42,X43,X44),esk10_6(X39,X40,X41,X42,X43,X44),esk11_6(X39,X40,X41,X42,X43,X44),esk12_6(X39,X40,X41,X42,X43,X44))|X44=k8_mcart_1(X39,X40,X41,X42,X43)|~m1_subset_1(X44,X39)|~m1_subset_1(X43,k4_zfmisc_1(X39,X40,X41,X42))|(X39=k1_xboole_0|X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0))&(X44!=esk9_6(X39,X40,X41,X42,X43,X44)|X44=k8_mcart_1(X39,X40,X41,X42,X43)|~m1_subset_1(X44,X39)|~m1_subset_1(X43,k4_zfmisc_1(X39,X40,X41,X42))|(X39=k1_xboole_0|X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_mcart_1])])])])])])).
% 0.21/0.39  fof(c_0_33, plain, ![X77, X78, X79, X80, X81]:(~m1_subset_1(X81,k4_zfmisc_1(X77,X78,X79,X80))|m1_subset_1(k8_mcart_1(X77,X78,X79,X80,X81),X77)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (k8_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk22_0|k9_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk23_0|k10_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk24_0|k11_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk25_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_35, negated_conjecture, (k11_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)=esk25_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.21/0.39  cnf(c_0_36, negated_conjecture, (k10_mcart_1(X1,X2,X3,X4,esk21_0)=esk24_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk21_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_29, c_0_18])).
% 0.21/0.39  cnf(c_0_37, plain, (k9_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8))=X6|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])]), c_0_31])).
% 0.21/0.39  cnf(c_0_38, plain, (X1=X7|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|X1!=k8_mcart_1(X2,X3,X4,X5,X6)|X6!=k4_mcart_1(X7,X8,X9,X10)|~m1_subset_1(X1,X2)|~m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.39  cnf(c_0_39, plain, (m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (k10_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk24_0|k8_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk22_0|k9_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk23_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.21/0.39  cnf(c_0_41, negated_conjecture, (k10_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)=esk24_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (k9_mcart_1(X1,X2,X3,X4,esk21_0)=esk23_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk21_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_37, c_0_18])).
% 0.21/0.39  cnf(c_0_43, plain, (k8_mcart_1(X1,X2,X3,X4,k4_mcart_1(X5,X6,X7,X8))=X5|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X1,X2,X3,X4))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])]), c_0_39])).
% 0.21/0.39  cnf(c_0_44, negated_conjecture, (k8_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk22_0|k9_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk23_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 0.21/0.39  cnf(c_0_45, negated_conjecture, (k9_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)=esk23_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (k8_mcart_1(X1,X2,X3,X4,esk21_0)=esk22_0|X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk21_0,k4_zfmisc_1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_43, c_0_18])).
% 0.21/0.39  cnf(c_0_47, negated_conjecture, (k8_mcart_1(esk17_0,esk18_0,esk19_0,esk20_0,esk21_0)!=esk22_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_24]), c_0_47]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 49
% 0.21/0.39  # Proof object clause steps            : 30
% 0.21/0.39  # Proof object formula steps           : 19
% 0.21/0.39  # Proof object conjectures             : 21
% 0.21/0.39  # Proof object clause conjectures      : 18
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 15
% 0.21/0.39  # Proof object initial formulas used   : 9
% 0.21/0.39  # Proof object generating inferences   : 8
% 0.21/0.39  # Proof object simplifying inferences  : 35
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 9
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 23
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 23
% 0.21/0.39  # Processed clauses                    : 79
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 1
% 0.21/0.39  # ...remaining for further processing  : 78
% 0.21/0.39  # Other redundant clauses eliminated   : 8
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 8
% 0.21/0.39  # Generated clauses                    : 87
% 0.21/0.39  # ...of the previous two non-trivial   : 94
% 0.21/0.39  # Contextual simplify-reflections      : 4
% 0.21/0.39  # Paramodulations                      : 83
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 8
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 43
% 0.21/0.40  #    Positive orientable unit clauses  : 8
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 5
% 0.21/0.40  #    Non-unit-clauses                  : 30
% 0.21/0.40  # Current number of unprocessed clauses: 61
% 0.21/0.40  # ...number of literals in the above   : 343
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 31
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 160
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 47
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 5
% 0.21/0.40  # Unit Clause-clause subsumption calls : 49
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 3
% 0.21/0.40  # BW rewrite match successes           : 3
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 6311
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.035 s
% 0.21/0.40  # System time              : 0.005 s
% 0.21/0.40  # Total time               : 0.039 s
% 0.21/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
