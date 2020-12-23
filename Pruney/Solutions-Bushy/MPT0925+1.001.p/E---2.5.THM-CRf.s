%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0925+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:25 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 441 expanded)
%              Number of clauses        :   49 ( 223 expanded)
%              Number of leaves         :    6 ( 100 expanded)
%              Depth                    :   21
%              Number of atoms          :  236 (2996 expanded)
%              Number of equality atoms :   54 ( 945 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t85_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( ! [X6] :
          ( r2_hidden(X6,X1)
        <=> ? [X7,X8,X9,X10] :
              ( r2_hidden(X7,X2)
              & r2_hidden(X8,X3)
              & r2_hidden(X9,X4)
              & r2_hidden(X10,X5)
              & X6 = k4_mcart_1(X7,X8,X9,X10) ) )
     => X1 = k4_zfmisc_1(X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(t72_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))
        & ! [X5,X6,X7] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & r2_hidden(X7,X4)
              & X1 = k3_mcart_1(X5,X6,X7) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(t73_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
    <=> ( r2_hidden(X1,X4)
        & r2_hidden(X2,X5)
        & r2_hidden(X3,X6) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_mcart_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( ! [X6] :
            ( r2_hidden(X6,X1)
          <=> ? [X7,X8,X9,X10] :
                ( r2_hidden(X7,X2)
                & r2_hidden(X8,X3)
                & r2_hidden(X9,X4)
                & r2_hidden(X10,X5)
                & X6 = k4_mcart_1(X7,X8,X9,X10) ) )
       => X1 = k4_zfmisc_1(X2,X3,X4,X5) ) ),
    inference(assume_negation,[status(cth)],[t85_mcart_1])).

fof(c_0_7,negated_conjecture,(
    ! [X54,X59,X60,X61,X62] :
      ( ( r2_hidden(esk14_1(X54),esk10_0)
        | ~ r2_hidden(X54,esk9_0) )
      & ( r2_hidden(esk15_1(X54),esk11_0)
        | ~ r2_hidden(X54,esk9_0) )
      & ( r2_hidden(esk16_1(X54),esk12_0)
        | ~ r2_hidden(X54,esk9_0) )
      & ( r2_hidden(esk17_1(X54),esk13_0)
        | ~ r2_hidden(X54,esk9_0) )
      & ( X54 = k4_mcart_1(esk14_1(X54),esk15_1(X54),esk16_1(X54),esk17_1(X54))
        | ~ r2_hidden(X54,esk9_0) )
      & ( ~ r2_hidden(X59,esk10_0)
        | ~ r2_hidden(X60,esk11_0)
        | ~ r2_hidden(X61,esk12_0)
        | ~ r2_hidden(X62,esk13_0)
        | X54 != k4_mcart_1(X59,X60,X61,X62)
        | r2_hidden(X54,esk9_0) )
      & esk9_0 != k4_zfmisc_1(esk10_0,esk11_0,esk12_0,esk13_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_8,plain,(
    ! [X28,X29,X30,X31] : k4_mcart_1(X28,X29,X30,X31) = k4_tarski(k3_mcart_1(X28,X29,X30),X31) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(X5,esk9_0)
    | ~ r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X3,esk12_0)
    | ~ r2_hidden(X4,esk13_0)
    | X5 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(X5,esk9_0)
    | X5 != k4_tarski(k3_mcart_1(X1,X2,X3),X4)
    | ~ r2_hidden(X4,esk13_0)
    | ~ r2_hidden(X3,esk12_0)
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_12,plain,(
    ! [X36,X37,X38,X39] :
      ( ( r2_hidden(esk6_4(X36,X37,X38,X39),X37)
        | ~ r2_hidden(X36,k3_zfmisc_1(X37,X38,X39)) )
      & ( r2_hidden(esk7_4(X36,X37,X38,X39),X38)
        | ~ r2_hidden(X36,k3_zfmisc_1(X37,X38,X39)) )
      & ( r2_hidden(esk8_4(X36,X37,X38,X39),X39)
        | ~ r2_hidden(X36,k3_zfmisc_1(X37,X38,X39)) )
      & ( X36 = k3_mcart_1(esk6_4(X36,X37,X38,X39),esk7_4(X36,X37,X38,X39),esk8_4(X36,X37,X38,X39))
        | ~ r2_hidden(X36,k3_zfmisc_1(X37,X38,X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_mcart_1])])])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(k4_tarski(k3_mcart_1(X1,X2,X3),X4),esk9_0)
    | ~ r2_hidden(X4,esk13_0)
    | ~ r2_hidden(X3,esk12_0)
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( X1 = k3_mcart_1(esk6_4(X1,X2,X3,X4),esk7_4(X1,X2,X3,X4),esk8_4(X1,X2,X3,X4))
    | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk9_0)
    | ~ r2_hidden(esk8_4(X1,X3,X4,X5),esk12_0)
    | ~ r2_hidden(esk7_4(X1,X3,X4,X5),esk11_0)
    | ~ r2_hidden(esk6_4(X1,X3,X4,X5),esk10_0)
    | ~ r2_hidden(X1,k3_zfmisc_1(X3,X4,X5))
    | ~ r2_hidden(X2,esk13_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,plain,
    ( r2_hidden(esk8_4(X1,X2,X3,X4),X4)
    | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk9_0)
    | ~ r2_hidden(esk7_4(X1,X3,X4,esk12_0),esk11_0)
    | ~ r2_hidden(esk6_4(X1,X3,X4,esk12_0),esk10_0)
    | ~ r2_hidden(X1,k3_zfmisc_1(X3,X4,esk12_0))
    | ~ r2_hidden(X2,esk13_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_18,plain,
    ( r2_hidden(esk7_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X11,X12,X13,X14,X17,X18,X19,X20,X21,X22,X24,X25] :
      ( ( r2_hidden(esk1_4(X11,X12,X13,X14),X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( r2_hidden(esk2_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( X14 = k4_tarski(esk1_4(X11,X12,X13,X14),esk2_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( ~ r2_hidden(X18,X11)
        | ~ r2_hidden(X19,X12)
        | X17 != k4_tarski(X18,X19)
        | r2_hidden(X17,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | ~ r2_hidden(X24,X20)
        | ~ r2_hidden(X25,X21)
        | esk3_3(X20,X21,X22) != k4_tarski(X24,X25)
        | X22 = k2_zfmisc_1(X20,X21) )
      & ( r2_hidden(esk4_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k2_zfmisc_1(X20,X21) )
      & ( r2_hidden(esk5_3(X20,X21,X22),X21)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k2_zfmisc_1(X20,X21) )
      & ( esk3_3(X20,X21,X22) = k4_tarski(esk4_3(X20,X21,X22),esk5_3(X20,X21,X22))
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k2_zfmisc_1(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk9_0)
    | ~ r2_hidden(esk6_4(X1,X3,esk11_0,esk12_0),esk10_0)
    | ~ r2_hidden(X1,k3_zfmisc_1(X3,esk11_0,esk12_0))
    | ~ r2_hidden(X2,esk13_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk9_0)
    | ~ r2_hidden(X1,k3_zfmisc_1(esk10_0,esk11_0,esk12_0))
    | ~ r2_hidden(X2,esk13_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

cnf(c_0_28,plain,
    ( esk3_3(X1,X2,X3) = k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(esk1_4(X2,X3,k2_zfmisc_1(X2,X3),X1),k3_zfmisc_1(esk10_0,esk11_0,esk12_0))
    | ~ r2_hidden(esk2_4(X2,X3,k2_zfmisc_1(X2,X3),X1),esk13_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( X1 = k2_zfmisc_1(X2,X3)
    | r2_hidden(esk3_3(X2,X3,X1),k2_zfmisc_1(X4,X5))
    | r2_hidden(esk3_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk5_3(X2,X3,X1),X5)
    | ~ r2_hidden(esk4_3(X2,X3,X1),X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(esk2_4(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),X2,k2_zfmisc_1(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),X2),X1),esk13_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( X1 = k2_zfmisc_1(X2,X3)
    | r2_hidden(esk3_3(X2,X3,X1),k2_zfmisc_1(X4,X3))
    | r2_hidden(esk3_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk4_3(X2,X3,X1),X4) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_38,plain,(
    ! [X32,X33,X34,X35] : k4_zfmisc_1(X32,X33,X34,X35) = k2_zfmisc_1(k3_zfmisc_1(X32,X33,X34),X35) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( X1 = k2_zfmisc_1(X2,X3)
    | r2_hidden(esk3_3(X2,X3,X1),k2_zfmisc_1(X2,X3))
    | r2_hidden(esk3_3(X2,X3,X1),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( esk9_0 != k4_zfmisc_1(esk10_0,esk11_0,esk12_0,esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_42,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( X1 = k2_zfmisc_1(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0)
    | r2_hidden(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,X1),esk9_0)
    | r2_hidden(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( esk9_0 != k2_zfmisc_1(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( X3 = k2_zfmisc_1(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X5,X2)
    | esk3_3(X1,X2,X3) != k4_tarski(X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_43]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( X1 = k4_mcart_1(esk14_1(X1),esk15_1(X1),esk16_1(X1),esk17_1(X1))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_48,negated_conjecture,
    ( esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0) != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,k3_zfmisc_1(esk10_0,esk11_0,esk12_0))
    | ~ r2_hidden(X2,esk13_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( X1 = k4_tarski(k3_mcart_1(esk14_1(X1),esk15_1(X1),esk16_1(X1)),esk17_1(X1))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_10])).

fof(c_0_50,plain,(
    ! [X43,X44,X45,X46,X47,X48] :
      ( ( r2_hidden(X43,X46)
        | ~ r2_hidden(k3_mcart_1(X43,X44,X45),k3_zfmisc_1(X46,X47,X48)) )
      & ( r2_hidden(X44,X47)
        | ~ r2_hidden(k3_mcart_1(X43,X44,X45),k3_zfmisc_1(X46,X47,X48)) )
      & ( r2_hidden(X45,X48)
        | ~ r2_hidden(k3_mcart_1(X43,X44,X45),k3_zfmisc_1(X46,X47,X48)) )
      & ( ~ r2_hidden(X43,X46)
        | ~ r2_hidden(X44,X47)
        | ~ r2_hidden(X45,X48)
        | r2_hidden(k3_mcart_1(X43,X44,X45),k3_zfmisc_1(X46,X47,X48)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_mcart_1])])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(k3_mcart_1(esk14_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk15_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk16_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0))),k3_zfmisc_1(esk10_0,esk11_0,esk12_0))
    | ~ r2_hidden(esk17_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49])]),c_0_46])])).

cnf(c_0_52,plain,
    ( r2_hidden(k3_mcart_1(X1,X3,X5),k3_zfmisc_1(X2,X4,X6))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk17_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk13_0)
    | ~ r2_hidden(esk16_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk12_0)
    | ~ r2_hidden(esk15_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk11_0)
    | ~ r2_hidden(esk14_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk10_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk17_1(X1),esk13_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk16_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk12_0)
    | ~ r2_hidden(esk15_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk11_0)
    | ~ r2_hidden(esk14_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_46])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk16_1(X1),esk12_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(esk15_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk11_0)
    | ~ r2_hidden(esk14_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_46])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk15_1(X1),esk11_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(esk14_1(esk3_3(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0,esk9_0)),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_46])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk14_1(X1),esk10_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_46])]),
    [proof]).

%------------------------------------------------------------------------------
