%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t48_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:08 EDT 2019

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t48_mcart_1.p',t48_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t48_mcart_1.p',d7_mcart_1)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t48_mcart_1.p',dt_k7_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t48_mcart_1.p',l44_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t48_mcart_1.p',d6_mcart_1)).

fof(dt_k6_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t48_mcart_1.p',dt_k6_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t48_mcart_1.p',d5_mcart_1)).

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t48_mcart_1.p',dt_k5_mcart_1)).

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
    ! [X37,X38,X39,X40,X41,X42,X43,X44] :
      ( ( X41 != k7_mcart_1(X37,X38,X39,X40)
        | X40 != k3_mcart_1(X42,X43,X44)
        | X41 = X44
        | ~ m1_subset_1(X41,X39)
        | ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 )
      & ( X40 = k3_mcart_1(esk11_5(X37,X38,X39,X40,X41),esk12_5(X37,X38,X39,X40,X41),esk13_5(X37,X38,X39,X40,X41))
        | X41 = k7_mcart_1(X37,X38,X39,X40)
        | ~ m1_subset_1(X41,X39)
        | ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 )
      & ( X41 != esk13_5(X37,X38,X39,X40,X41)
        | X41 = k7_mcart_1(X37,X38,X39,X40)
        | ~ m1_subset_1(X41,X39)
        | ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_mcart_1])])])])])).

fof(c_0_10,plain,(
    ! [X56,X57,X58,X59] :
      ( ~ m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))
      | m1_subset_1(k7_mcart_1(X56,X57,X58,X59),X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

fof(c_0_11,plain,(
    ! [X62,X63,X64,X65] :
      ( ( m1_subset_1(esk15_4(X62,X63,X64,X65),X62)
        | ~ m1_subset_1(X65,k3_zfmisc_1(X62,X63,X64))
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0 )
      & ( m1_subset_1(esk16_4(X62,X63,X64,X65),X63)
        | ~ m1_subset_1(X65,k3_zfmisc_1(X62,X63,X64))
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0 )
      & ( m1_subset_1(esk17_4(X62,X63,X64,X65),X64)
        | ~ m1_subset_1(X65,k3_zfmisc_1(X62,X63,X64))
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0 )
      & ( X65 = k3_mcart_1(esk15_4(X62,X63,X64,X65),esk16_4(X62,X63,X64,X65),esk17_4(X62,X63,X64,X65))
        | ~ m1_subset_1(X65,k3_zfmisc_1(X62,X63,X64))
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).

fof(c_0_12,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
    & esk4_0 != k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
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
    ( X1 = k3_mcart_1(esk15_4(X2,X3,X4,X1),esk16_4(X2,X3,X4,X1),esk17_4(X2,X3,X4,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k7_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X6
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])]),c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k3_mcart_1(esk15_4(esk1_0,esk2_0,esk3_0,esk4_0),esk16_4(esk1_0,esk2_0,esk3_0,esk4_0),esk17_4(esk1_0,esk2_0,esk3_0,esk4_0)) = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

fof(c_0_22,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( X30 != k6_mcart_1(X26,X27,X28,X29)
        | X29 != k3_mcart_1(X31,X32,X33)
        | X30 = X32
        | ~ m1_subset_1(X30,X27)
        | ~ m1_subset_1(X29,k3_zfmisc_1(X26,X27,X28))
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( X29 = k3_mcart_1(esk8_5(X26,X27,X28,X29,X30),esk9_5(X26,X27,X28,X29,X30),esk10_5(X26,X27,X28,X29,X30))
        | X30 = k6_mcart_1(X26,X27,X28,X29)
        | ~ m1_subset_1(X30,X27)
        | ~ m1_subset_1(X29,k3_zfmisc_1(X26,X27,X28))
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( X30 != esk9_5(X26,X27,X28,X29,X30)
        | X30 = k6_mcart_1(X26,X27,X28,X29)
        | ~ m1_subset_1(X30,X27)
        | ~ m1_subset_1(X29,k3_zfmisc_1(X26,X27,X28))
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_mcart_1])])])])])])).

fof(c_0_23,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ m1_subset_1(X55,k3_zfmisc_1(X52,X53,X54))
      | m1_subset_1(k6_mcart_1(X52,X53,X54,X55),X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).

cnf(c_0_24,negated_conjecture,
    ( k7_mcart_1(X1,X2,X3,esk4_0) = esk17_4(esk1_0,esk2_0,esk3_0,esk4_0)
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k3_zfmisc_1(X1,X2,X3)) ),
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
    ( esk17_4(esk1_0,esk2_0,esk3_0,esk4_0) = k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_28,plain,
    ( k6_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X5
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( k3_mcart_1(esk15_4(esk1_0,esk2_0,esk3_0,esk4_0),esk16_4(esk1_0,esk2_0,esk3_0,esk4_0),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_27])).

fof(c_0_30,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( X19 != k5_mcart_1(X15,X16,X17,X18)
        | X18 != k3_mcart_1(X20,X21,X22)
        | X19 = X20
        | ~ m1_subset_1(X19,X15)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X18 = k3_mcart_1(esk5_5(X15,X16,X17,X18,X19),esk6_5(X15,X16,X17,X18,X19),esk7_5(X15,X16,X17,X18,X19))
        | X19 = k5_mcart_1(X15,X16,X17,X18)
        | ~ m1_subset_1(X19,X15)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X19 != esk5_5(X15,X16,X17,X18,X19)
        | X19 = k5_mcart_1(X15,X16,X17,X18)
        | ~ m1_subset_1(X19,X15)
        | ~ m1_subset_1(X18,k3_zfmisc_1(X15,X16,X17))
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_mcart_1])])])])])])).

fof(c_0_31,plain,(
    ! [X48,X49,X50,X51] :
      ( ~ m1_subset_1(X51,k3_zfmisc_1(X48,X49,X50))
      | m1_subset_1(k5_mcart_1(X48,X49,X50,X51),X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

cnf(c_0_32,negated_conjecture,
    ( k6_mcart_1(X1,X2,X3,esk4_0) = esk16_4(esk1_0,esk2_0,esk3_0,esk4_0)
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k3_zfmisc_1(X1,X2,X3)) ),
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
    ( esk16_4(esk1_0,esk2_0,esk3_0,esk4_0) = k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_36,plain,
    ( k5_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X4
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( k3_mcart_1(esk15_4(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( k5_mcart_1(X1,X2,X3,esk4_0) = esk15_4(esk1_0,esk2_0,esk3_0,esk4_0)
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( esk15_4(esk1_0,esk2_0,esk3_0,esk4_0) = k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( esk4_0 != k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_39]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
