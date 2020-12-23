%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:54 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 977 expanded)
%              Number of clauses        :   45 ( 417 expanded)
%              Number of leaves         :    9 ( 238 expanded)
%              Depth                    :   15
%              Number of atoms          :  190 (3701 expanded)
%              Number of equality atoms :  117 (2844 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
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

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X38,X39,X40,X41] :
      ( X38 = k1_xboole_0
      | X39 = k1_xboole_0
      | X40 = k1_xboole_0
      | ~ m1_subset_1(X41,k3_zfmisc_1(X38,X39,X40))
      | X41 = k3_mcart_1(k5_mcart_1(X38,X39,X40,X41),k6_mcart_1(X38,X39,X40,X41),k7_mcart_1(X38,X39,X40,X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_11,plain,(
    ! [X24,X25,X26] : k3_mcart_1(X24,X25,X26) = k4_tarski(k4_tarski(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_12,plain,(
    ! [X27,X28,X29] : k3_zfmisc_1(X27,X28,X29) = k2_zfmisc_1(k2_zfmisc_1(X27,X28),X29) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_13,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
      | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X42,X43] :
      ( k1_mcart_1(k4_tarski(X42,X43)) = X42
      & k2_mcart_1(k4_tarski(X42,X43)) = X43 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_19,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_24,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X15
        | X16 != k1_tarski(X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k1_tarski(X15) )
      & ( ~ r2_hidden(esk2_2(X19,X20),X20)
        | esk2_2(X19,X20) != X19
        | X20 = k1_tarski(X19) )
      & ( r2_hidden(esk2_2(X19,X20),X20)
        | esk2_2(X19,X20) = X19
        | X20 = k1_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_25,plain,(
    ! [X33,X35,X36,X37] :
      ( ( r2_hidden(esk3_1(X33),X33)
        | X33 = k1_xboole_0 )
      & ( ~ r2_hidden(X35,X33)
        | esk3_1(X33) != k3_mcart_1(X35,X36,X37)
        | X33 = k1_xboole_0 )
      & ( ~ r2_hidden(X36,X33)
        | esk3_1(X33) != k3_mcart_1(X35,X36,X37)
        | X33 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_26,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X30,X31,X32] :
      ( ( X30 != k1_mcart_1(X30)
        | X30 != k4_tarski(X31,X32) )
      & ( X30 != k2_mcart_1(X30)
        | X30 != k4_tarski(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

cnf(c_0_30,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = k2_mcart_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).

cnf(c_0_34,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( X2 = k1_xboole_0
    | esk3_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r2_hidden(esk3_1(k1_tarski(X1)),k1_tarski(X1))
    | r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_26])).

cnf(c_0_42,plain,
    ( X2 = k1_xboole_0
    | esk3_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk3_1(X1) != esk7_0
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( esk3_1(k1_tarski(X1)) = X1
    | r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( esk7_0 = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)
    | esk7_0 = k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

fof(c_0_47,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_48,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk3_1(X1) != esk7_0
    | ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k1_tarski(esk7_0) = k1_xboole_0
    | r2_hidden(esk7_0,k1_xboole_0)
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk7_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_50,negated_conjecture,
    ( k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k1_tarski(esk7_0) = k1_xboole_0
    | r2_hidden(esk7_0,k1_xboole_0)
    | ~ r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk7_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_44])])).

cnf(c_0_53,negated_conjecture,
    ( k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0) = esk7_0
    | k1_tarski(esk7_0) = k1_xboole_0
    | r2_hidden(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_33])])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k1_tarski(esk7_0) = k1_xboole_0
    | r2_hidden(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_33])])).

cnf(c_0_56,plain,
    ( r2_hidden(esk3_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))
    | ~ r2_hidden(X3,k1_xboole_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_55])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_1(k4_xboole_0(X1,k1_xboole_0)),k4_xboole_0(X1,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_57])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(esk3_1(k4_xboole_0(X1,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_1(k4_xboole_0(X1,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_61,c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:53:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.41  # and selection function SelectNegativeLiterals.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.19/0.41  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.19/0.41  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.19/0.41  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.41  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.19/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.41  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.19/0.41  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.19/0.41  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.41  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.19/0.41  fof(c_0_10, plain, ![X38, X39, X40, X41]:(X38=k1_xboole_0|X39=k1_xboole_0|X40=k1_xboole_0|(~m1_subset_1(X41,k3_zfmisc_1(X38,X39,X40))|X41=k3_mcart_1(k5_mcart_1(X38,X39,X40,X41),k6_mcart_1(X38,X39,X40,X41),k7_mcart_1(X38,X39,X40,X41)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.19/0.41  fof(c_0_11, plain, ![X24, X25, X26]:k3_mcart_1(X24,X25,X26)=k4_tarski(k4_tarski(X24,X25),X26), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.19/0.41  fof(c_0_12, plain, ![X27, X28, X29]:k3_zfmisc_1(X27,X28,X29)=k2_zfmisc_1(k2_zfmisc_1(X27,X28),X29), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.41  fof(c_0_13, negated_conjecture, (((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&(m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.41  cnf(c_0_14, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  cnf(c_0_15, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_16, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk7_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  fof(c_0_18, plain, ![X42, X43]:(k1_mcart_1(k4_tarski(X42,X43))=X42&k2_mcart_1(k4_tarski(X42,X43))=X43), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.19/0.41  cnf(c_0_19, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.19/0.41  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk7_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 0.19/0.41  cnf(c_0_21, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_22, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_23, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  fof(c_0_24, plain, ![X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X17,X16)|X17=X15|X16!=k1_tarski(X15))&(X18!=X15|r2_hidden(X18,X16)|X16!=k1_tarski(X15)))&((~r2_hidden(esk2_2(X19,X20),X20)|esk2_2(X19,X20)!=X19|X20=k1_tarski(X19))&(r2_hidden(esk2_2(X19,X20),X20)|esk2_2(X19,X20)=X19|X20=k1_tarski(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.41  fof(c_0_25, plain, ![X33, X35, X36, X37]:((r2_hidden(esk3_1(X33),X33)|X33=k1_xboole_0)&((~r2_hidden(X35,X33)|esk3_1(X33)!=k3_mcart_1(X35,X36,X37)|X33=k1_xboole_0)&(~r2_hidden(X36,X33)|esk3_1(X33)!=k3_mcart_1(X35,X36,X37)|X33=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.19/0.41  cnf(c_0_26, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0))=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.19/0.41  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  fof(c_0_29, plain, ![X30, X31, X32]:((X30!=k1_mcart_1(X30)|X30!=k4_tarski(X31,X32))&(X30!=k2_mcart_1(X30)|X30!=k4_tarski(X31,X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.19/0.41  cnf(c_0_30, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=k2_mcart_1(esk7_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.41  cnf(c_0_32, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_33, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).
% 0.19/0.41  cnf(c_0_34, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.41  cnf(c_0_35, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_36, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.41  cnf(c_0_37, plain, (X2=k1_xboole_0|esk3_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_15])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)),k2_mcart_1(esk7_0))=esk7_0), inference(rw,[status(thm)],[c_0_27, c_0_31])).
% 0.19/0.41  cnf(c_0_39, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_40, plain, (r2_hidden(esk3_1(k1_tarski(X1)),k1_tarski(X1))|r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.41  cnf(c_0_41, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_35]), c_0_26])).
% 0.19/0.41  cnf(c_0_42, plain, (X2=k1_xboole_0|esk3_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_15])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (X1=k1_xboole_0|esk3_1(X1)!=esk7_0|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.41  cnf(c_0_44, plain, (esk3_1(k1_tarski(X1))=X1|r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (esk7_0=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)|esk7_0=k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)!=esk7_0), inference(spm,[status(thm)],[c_0_41, c_0_27])).
% 0.19/0.41  fof(c_0_47, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (X1=k1_xboole_0|esk3_1(X1)!=esk7_0|~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_42, c_0_38])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (k1_tarski(esk7_0)=k1_xboole_0|r2_hidden(esk7_0,k1_xboole_0)|~r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk7_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44])])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (k6_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.41  cnf(c_0_51, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (k1_tarski(esk7_0)=k1_xboole_0|r2_hidden(esk7_0,k1_xboole_0)|~r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk7_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_44])])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (k5_mcart_1(esk4_0,esk5_0,esk6_0,esk7_0)=esk7_0|k1_tarski(esk7_0)=k1_xboole_0|r2_hidden(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_33])])).
% 0.19/0.41  cnf(c_0_54, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_51])).
% 0.19/0.41  cnf(c_0_55, negated_conjecture, (k1_tarski(esk7_0)=k1_xboole_0|r2_hidden(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_33])])).
% 0.19/0.41  cnf(c_0_56, plain, (r2_hidden(esk3_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))|~r2_hidden(X3,k1_xboole_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_54, c_0_34])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (r2_hidden(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_55])).
% 0.19/0.41  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_1(k4_xboole_0(X1,k1_xboole_0)),k4_xboole_0(X1,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_57])])).
% 0.19/0.41  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_58])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (~r2_hidden(esk3_1(k4_xboole_0(X1,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_59])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (r2_hidden(esk3_1(k4_xboole_0(X1,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_60, c_0_59])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_61, c_0_62]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 64
% 0.19/0.41  # Proof object clause steps            : 45
% 0.19/0.41  # Proof object formula steps           : 19
% 0.19/0.41  # Proof object conjectures             : 25
% 0.19/0.41  # Proof object clause conjectures      : 22
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 17
% 0.19/0.41  # Proof object initial formulas used   : 9
% 0.19/0.41  # Proof object generating inferences   : 17
% 0.19/0.41  # Proof object simplifying inferences  : 25
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 10
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 27
% 0.19/0.41  # Removed in clause preprocessing      : 2
% 0.19/0.41  # Initial clauses in saturation        : 25
% 0.19/0.41  # Processed clauses                    : 298
% 0.19/0.41  # ...of these trivial                  : 6
% 0.19/0.41  # ...subsumed                          : 84
% 0.19/0.41  # ...remaining for further processing  : 208
% 0.19/0.41  # Other redundant clauses eliminated   : 201
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 5
% 0.19/0.41  # Backward-rewritten                   : 5
% 0.19/0.41  # Generated clauses                    : 3227
% 0.19/0.41  # ...of the previous two non-trivial   : 2459
% 0.19/0.41  # Contextual simplify-reflections      : 0
% 0.19/0.41  # Paramodulations                      : 3026
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 201
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 165
% 0.19/0.41  #    Positive orientable unit clauses  : 21
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 10
% 0.19/0.41  #    Non-unit-clauses                  : 134
% 0.19/0.41  # Current number of unprocessed clauses: 2163
% 0.19/0.41  # ...number of literals in the above   : 7523
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 38
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 2039
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1564
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 66
% 0.19/0.41  # Unit Clause-clause subsumption calls : 171
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 14
% 0.19/0.41  # BW rewrite match successes           : 3
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 45610
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.068 s
% 0.19/0.41  # System time              : 0.008 s
% 0.19/0.41  # Total time               : 0.076 s
% 0.19/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
