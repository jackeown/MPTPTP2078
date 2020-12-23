%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0914+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:24 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 366 expanded)
%              Number of clauses        :   41 ( 193 expanded)
%              Number of leaves         :    4 (  79 expanded)
%              Depth                    :   19
%              Number of atoms          :  177 (2679 expanded)
%              Number of equality atoms :   51 ( 998 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ! [X5] :
          ( r2_hidden(X5,X1)
        <=> ? [X6,X7,X8] :
              ( r2_hidden(X6,X2)
              & r2_hidden(X7,X3)
              & r2_hidden(X8,X4)
              & X5 = k3_mcart_1(X6,X7,X8) ) )
     => X1 = k3_zfmisc_1(X2,X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

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

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ! [X5] :
            ( r2_hidden(X5,X1)
          <=> ? [X6,X7,X8] :
                ( r2_hidden(X6,X2)
                & r2_hidden(X7,X3)
                & r2_hidden(X8,X4)
                & X5 = k3_mcart_1(X6,X7,X8) ) )
       => X1 = k3_zfmisc_1(X2,X3,X4) ) ),
    inference(assume_negation,[status(cth)],[t74_mcart_1])).

fof(c_0_5,negated_conjecture,(
    ! [X36,X40,X41,X42] :
      ( ( r2_hidden(esk10_1(X36),esk7_0)
        | ~ r2_hidden(X36,esk6_0) )
      & ( r2_hidden(esk11_1(X36),esk8_0)
        | ~ r2_hidden(X36,esk6_0) )
      & ( r2_hidden(esk12_1(X36),esk9_0)
        | ~ r2_hidden(X36,esk6_0) )
      & ( X36 = k3_mcart_1(esk10_1(X36),esk11_1(X36),esk12_1(X36))
        | ~ r2_hidden(X36,esk6_0) )
      & ( ~ r2_hidden(X40,esk7_0)
        | ~ r2_hidden(X41,esk8_0)
        | ~ r2_hidden(X42,esk9_0)
        | X36 != k3_mcart_1(X40,X41,X42)
        | r2_hidden(X36,esk6_0) )
      & esk6_0 != k3_zfmisc_1(esk7_0,esk8_0,esk9_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])])).

fof(c_0_6,plain,(
    ! [X26,X27,X28] : k3_mcart_1(X26,X27,X28) = k4_tarski(k4_tarski(X26,X27),X28) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(X4,esk6_0)
    | ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X3,esk9_0)
    | X4 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X9,X10,X11,X12,X15,X16,X17,X18,X19,X20,X22,X23] :
      ( ( r2_hidden(esk1_4(X9,X10,X11,X12),X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k2_zfmisc_1(X9,X10) )
      & ( r2_hidden(esk2_4(X9,X10,X11,X12),X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k2_zfmisc_1(X9,X10) )
      & ( X12 = k4_tarski(esk1_4(X9,X10,X11,X12),esk2_4(X9,X10,X11,X12))
        | ~ r2_hidden(X12,X11)
        | X11 != k2_zfmisc_1(X9,X10) )
      & ( ~ r2_hidden(X16,X9)
        | ~ r2_hidden(X17,X10)
        | X15 != k4_tarski(X16,X17)
        | r2_hidden(X15,X11)
        | X11 != k2_zfmisc_1(X9,X10) )
      & ( ~ r2_hidden(esk3_3(X18,X19,X20),X20)
        | ~ r2_hidden(X22,X18)
        | ~ r2_hidden(X23,X19)
        | esk3_3(X18,X19,X20) != k4_tarski(X22,X23)
        | X20 = k2_zfmisc_1(X18,X19) )
      & ( r2_hidden(esk4_3(X18,X19,X20),X18)
        | r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k2_zfmisc_1(X18,X19) )
      & ( r2_hidden(esk5_3(X18,X19,X20),X19)
        | r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k2_zfmisc_1(X18,X19) )
      & ( esk3_3(X18,X19,X20) = k4_tarski(esk4_3(X18,X19,X20),esk5_3(X18,X19,X20))
        | r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k2_zfmisc_1(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(X4,esk6_0)
    | X4 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(X1,X2),X3),esk6_0)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk6_0)
    | ~ r2_hidden(esk2_4(X3,X4,k2_zfmisc_1(X3,X4),X1),esk8_0)
    | ~ r2_hidden(esk1_4(X3,X4,k2_zfmisc_1(X3,X4),X1),esk7_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk6_0)
    | ~ r2_hidden(esk1_4(X3,esk8_0,k2_zfmisc_1(X3,esk8_0),X1),esk7_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,esk8_0))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk6_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(esk7_0,esk8_0))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_23,plain,
    ( esk3_3(X1,X2,X3) = k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(esk1_4(X2,X3,k2_zfmisc_1(X2,X3),X1),k2_zfmisc_1(esk7_0,esk8_0))
    | ~ r2_hidden(esk2_4(X2,X3,k2_zfmisc_1(X2,X3),X1),esk9_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_25,plain,
    ( X1 = k2_zfmisc_1(X2,X3)
    | r2_hidden(esk3_3(X2,X3,X1),k2_zfmisc_1(X4,X5))
    | r2_hidden(esk3_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk5_3(X2,X3,X1),X5)
    | ~ r2_hidden(esk4_3(X2,X3,X1),X4) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(esk2_4(k2_zfmisc_1(esk7_0,esk8_0),X2,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X2),X1),esk9_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_28,plain,
    ( X1 = k2_zfmisc_1(X2,X3)
    | r2_hidden(esk3_3(X2,X3,X1),k2_zfmisc_1(X4,X3))
    | r2_hidden(esk3_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk4_3(X2,X3,X1),X4) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_30,plain,(
    ! [X29,X30,X31] : k3_zfmisc_1(X29,X30,X31) = k2_zfmisc_1(k2_zfmisc_1(X29,X30),X31) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_16])).

cnf(c_0_32,plain,
    ( X1 = k2_zfmisc_1(X2,X3)
    | r2_hidden(esk3_3(X2,X3,X1),k2_zfmisc_1(X2,X3))
    | r2_hidden(esk3_3(X2,X3,X1),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( esk6_0 != k3_zfmisc_1(esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_34,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( X1 = k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)
    | r2_hidden(esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,X1),esk6_0)
    | r2_hidden(esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( esk6_0 != k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( X3 = k2_zfmisc_1(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X5,X2)
    | esk3_3(X1,X2,X3) != k4_tarski(X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_35]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( X1 = k3_mcart_1(esk10_1(X1),esk11_1(X1),esk12_1(X1))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_40,negated_conjecture,
    ( esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,esk6_0) != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(esk7_0,esk8_0))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( X1 = k4_tarski(k4_tarski(esk10_1(X1),esk11_1(X1)),esk12_1(X1))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk10_1(esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,esk6_0)),esk11_1(esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,esk6_0))),k2_zfmisc_1(esk7_0,esk8_0))
    | ~ r2_hidden(esk12_1(esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,esk6_0)),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41])]),c_0_38])])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk12_1(esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,esk6_0)),esk9_0)
    | ~ r2_hidden(esk11_1(esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,esk6_0)),esk8_0)
    | ~ r2_hidden(esk10_1(esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk12_1(X1),esk9_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk11_1(esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,esk6_0)),esk8_0)
    | ~ r2_hidden(esk10_1(esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,esk6_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_38])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk11_1(X1),esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(esk10_1(esk3_3(k2_zfmisc_1(esk7_0,esk8_0),esk9_0,esk6_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_38])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk10_1(X1),esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_38])]),
    [proof]).

%------------------------------------------------------------------------------
