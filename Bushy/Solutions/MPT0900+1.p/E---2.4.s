%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t60_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:11 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t60_mcart_1.p',t60_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t60_mcart_1.p',d11_mcart_1)).

fof(dt_k11_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t60_mcart_1.p',dt_k11_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t60_mcart_1.p',l68_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t60_mcart_1.p',d10_mcart_1)).

fof(dt_k10_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t60_mcart_1.p',dt_k10_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t60_mcart_1.p',d9_mcart_1)).

fof(dt_k9_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t60_mcart_1.p',dt_k9_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/mcart_1__t60_mcart_1.p',d8_mcart_1)).

fof(dt_k8_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t60_mcart_1.p',dt_k8_mcart_1)).

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
    ! [X32,X33,X34,X35,X36,X37,X38,X39,X40,X41] :
      ( ( X37 != k11_mcart_1(X32,X33,X34,X35,X36)
        | X36 != k4_mcart_1(X38,X39,X40,X41)
        | X37 = X41
        | ~ m1_subset_1(X37,X35)
        | ~ m1_subset_1(X36,k4_zfmisc_1(X32,X33,X34,X35))
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0 )
      & ( X36 = k4_mcart_1(esk10_6(X32,X33,X34,X35,X36,X37),esk11_6(X32,X33,X34,X35,X36,X37),esk12_6(X32,X33,X34,X35,X36,X37),esk13_6(X32,X33,X34,X35,X36,X37))
        | X37 = k11_mcart_1(X32,X33,X34,X35,X36)
        | ~ m1_subset_1(X37,X35)
        | ~ m1_subset_1(X36,k4_zfmisc_1(X32,X33,X34,X35))
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0 )
      & ( X37 != esk13_6(X32,X33,X34,X35,X36,X37)
        | X37 = k11_mcart_1(X32,X33,X34,X35,X36)
        | ~ m1_subset_1(X37,X35)
        | ~ m1_subset_1(X36,k4_zfmisc_1(X32,X33,X34,X35))
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_mcart_1])])])])])).

fof(c_0_12,plain,(
    ! [X79,X80,X81,X82,X83] :
      ( ~ m1_subset_1(X83,k4_zfmisc_1(X79,X80,X81,X82))
      | m1_subset_1(k11_mcart_1(X79,X80,X81,X82,X83),X82) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).

fof(c_0_13,plain,(
    ! [X96,X97,X98,X99,X100] :
      ( ( m1_subset_1(esk23_5(X96,X97,X98,X99,X100),X96)
        | ~ m1_subset_1(X100,k4_zfmisc_1(X96,X97,X98,X99))
        | X96 = k1_xboole_0
        | X97 = k1_xboole_0
        | X98 = k1_xboole_0
        | X99 = k1_xboole_0 )
      & ( m1_subset_1(esk24_5(X96,X97,X98,X99,X100),X97)
        | ~ m1_subset_1(X100,k4_zfmisc_1(X96,X97,X98,X99))
        | X96 = k1_xboole_0
        | X97 = k1_xboole_0
        | X98 = k1_xboole_0
        | X99 = k1_xboole_0 )
      & ( m1_subset_1(esk25_5(X96,X97,X98,X99,X100),X98)
        | ~ m1_subset_1(X100,k4_zfmisc_1(X96,X97,X98,X99))
        | X96 = k1_xboole_0
        | X97 = k1_xboole_0
        | X98 = k1_xboole_0
        | X99 = k1_xboole_0 )
      & ( m1_subset_1(esk26_5(X96,X97,X98,X99,X100),X99)
        | ~ m1_subset_1(X100,k4_zfmisc_1(X96,X97,X98,X99))
        | X96 = k1_xboole_0
        | X97 = k1_xboole_0
        | X98 = k1_xboole_0
        | X99 = k1_xboole_0 )
      & ( X100 = k4_mcart_1(esk23_5(X96,X97,X98,X99,X100),esk24_5(X96,X97,X98,X99,X100),esk25_5(X96,X97,X98,X99,X100),esk26_5(X96,X97,X98,X99,X100))
        | ~ m1_subset_1(X100,k4_zfmisc_1(X96,X97,X98,X99))
        | X96 = k1_xboole_0
        | X97 = k1_xboole_0
        | X98 = k1_xboole_0
        | X99 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).

fof(c_0_14,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
    & esk5_0 != k4_mcart_1(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) ),
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
    ( X1 = k4_mcart_1(esk23_5(X2,X3,X4,X5,X1),esk24_5(X2,X3,X4,X5,X1),esk25_5(X2,X3,X4,X5,X1),esk26_5(X2,X3,X4,X5,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
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
    ( k4_mcart_1(esk23_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),esk24_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),esk25_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),esk26_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) = esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])).

fof(c_0_25,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( X23 != k10_mcart_1(X18,X19,X20,X21,X22)
        | X22 != k4_mcart_1(X24,X25,X26,X27)
        | X23 = X26
        | ~ m1_subset_1(X23,X20)
        | ~ m1_subset_1(X22,k4_zfmisc_1(X18,X19,X20,X21))
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 )
      & ( X22 = k4_mcart_1(esk6_6(X18,X19,X20,X21,X22,X23),esk7_6(X18,X19,X20,X21,X22,X23),esk8_6(X18,X19,X20,X21,X22,X23),esk9_6(X18,X19,X20,X21,X22,X23))
        | X23 = k10_mcart_1(X18,X19,X20,X21,X22)
        | ~ m1_subset_1(X23,X20)
        | ~ m1_subset_1(X22,k4_zfmisc_1(X18,X19,X20,X21))
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 )
      & ( X23 != esk8_6(X18,X19,X20,X21,X22,X23)
        | X23 = k10_mcart_1(X18,X19,X20,X21,X22)
        | ~ m1_subset_1(X23,X20)
        | ~ m1_subset_1(X22,k4_zfmisc_1(X18,X19,X20,X21))
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_mcart_1])])])])])])).

fof(c_0_26,plain,(
    ! [X74,X75,X76,X77,X78] :
      ( ~ m1_subset_1(X78,k4_zfmisc_1(X74,X75,X76,X77))
      | m1_subset_1(k10_mcart_1(X74,X75,X76,X77,X78),X76) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).

cnf(c_0_27,negated_conjecture,
    ( k11_mcart_1(X1,X2,X3,X4,esk5_0) = esk26_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
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
    ( esk26_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
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
    ( k4_mcart_1(esk23_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),esk24_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),esk25_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_30])).

fof(c_0_33,plain,(
    ! [X60,X61,X62,X63,X64,X65,X66,X67,X68,X69] :
      ( ( X65 != k9_mcart_1(X60,X61,X62,X63,X64)
        | X64 != k4_mcart_1(X66,X67,X68,X69)
        | X65 = X67
        | ~ m1_subset_1(X65,X61)
        | ~ m1_subset_1(X64,k4_zfmisc_1(X60,X61,X62,X63))
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0 )
      & ( X64 = k4_mcart_1(esk18_6(X60,X61,X62,X63,X64,X65),esk19_6(X60,X61,X62,X63,X64,X65),esk20_6(X60,X61,X62,X63,X64,X65),esk21_6(X60,X61,X62,X63,X64,X65))
        | X65 = k9_mcart_1(X60,X61,X62,X63,X64)
        | ~ m1_subset_1(X65,X61)
        | ~ m1_subset_1(X64,k4_zfmisc_1(X60,X61,X62,X63))
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0 )
      & ( X65 != esk19_6(X60,X61,X62,X63,X64,X65)
        | X65 = k9_mcart_1(X60,X61,X62,X63,X64)
        | ~ m1_subset_1(X65,X61)
        | ~ m1_subset_1(X64,k4_zfmisc_1(X60,X61,X62,X63))
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_mcart_1])])])])])])).

fof(c_0_34,plain,(
    ! [X89,X90,X91,X92,X93] :
      ( ~ m1_subset_1(X93,k4_zfmisc_1(X89,X90,X91,X92))
      | m1_subset_1(k9_mcart_1(X89,X90,X91,X92,X93),X90) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

cnf(c_0_35,negated_conjecture,
    ( k10_mcart_1(X1,X2,X3,X4,esk5_0) = esk25_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
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
    ( esk25_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
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
    ( k4_mcart_1(esk23_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),esk24_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_38])).

fof(c_0_41,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52,X53,X54,X55] :
      ( ( X51 != k8_mcart_1(X46,X47,X48,X49,X50)
        | X50 != k4_mcart_1(X52,X53,X54,X55)
        | X51 = X52
        | ~ m1_subset_1(X51,X46)
        | ~ m1_subset_1(X50,k4_zfmisc_1(X46,X47,X48,X49))
        | X46 = k1_xboole_0
        | X47 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0 )
      & ( X50 = k4_mcart_1(esk14_6(X46,X47,X48,X49,X50,X51),esk15_6(X46,X47,X48,X49,X50,X51),esk16_6(X46,X47,X48,X49,X50,X51),esk17_6(X46,X47,X48,X49,X50,X51))
        | X51 = k8_mcart_1(X46,X47,X48,X49,X50)
        | ~ m1_subset_1(X51,X46)
        | ~ m1_subset_1(X50,k4_zfmisc_1(X46,X47,X48,X49))
        | X46 = k1_xboole_0
        | X47 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0 )
      & ( X51 != esk14_6(X46,X47,X48,X49,X50,X51)
        | X51 = k8_mcart_1(X46,X47,X48,X49,X50)
        | ~ m1_subset_1(X51,X46)
        | ~ m1_subset_1(X50,k4_zfmisc_1(X46,X47,X48,X49))
        | X46 = k1_xboole_0
        | X47 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_mcart_1])])])])])])).

fof(c_0_42,plain,(
    ! [X84,X85,X86,X87,X88] :
      ( ~ m1_subset_1(X88,k4_zfmisc_1(X84,X85,X86,X87))
      | m1_subset_1(k8_mcart_1(X84,X85,X86,X87,X88),X84) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

cnf(c_0_43,negated_conjecture,
    ( k9_mcart_1(X1,X2,X3,X4,esk5_0) = esk24_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
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
    ( esk24_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
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
    ( k4_mcart_1(esk23_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( k8_mcart_1(X1,X2,X3,X4,esk5_0) = esk23_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( esk23_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( esk5_0 != k4_mcart_1(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_50]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
