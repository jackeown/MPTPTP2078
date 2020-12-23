%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t108_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:57 EDT 2019

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   23 (  70 expanded)
%              Number of clauses        :   16 (  31 expanded)
%              Number of leaves         :    3 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 309 expanded)
%              Number of equality atoms :   32 ( 107 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t108_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ! [X5,X6] :
          ( r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X1,X2))
        <=> r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X3,X4)) )
     => k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t108_zfmisc_1.p',t108_zfmisc_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t108_zfmisc_1.p',d2_zfmisc_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t108_zfmisc_1.p',t2_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ! [X5,X6] :
            ( r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X1,X2))
          <=> r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X3,X4)) )
       => k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4) ) ),
    inference(assume_negation,[status(cth)],[t108_zfmisc_1])).

fof(c_0_4,negated_conjecture,(
    ! [X11,X12] :
      ( ( ~ r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(esk1_0,esk2_0))
        | r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(esk3_0,esk4_0)) )
      & ( ~ r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(esk3_0,esk4_0))
        | r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(esk1_0,esk2_0)) )
      & k2_zfmisc_1(esk1_0,esk2_0) != k2_zfmisc_1(esk3_0,esk4_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

fof(c_0_5,plain,(
    ! [X15,X16,X17,X18,X21,X22,X23,X24,X25,X26,X28,X29] :
      ( ( r2_hidden(esk5_4(X15,X16,X17,X18),X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( r2_hidden(esk6_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( X18 = k4_tarski(esk5_4(X15,X16,X17,X18),esk6_4(X15,X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( ~ r2_hidden(X22,X15)
        | ~ r2_hidden(X23,X16)
        | X21 != k4_tarski(X22,X23)
        | r2_hidden(X21,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( ~ r2_hidden(esk7_3(X24,X25,X26),X26)
        | ~ r2_hidden(X28,X24)
        | ~ r2_hidden(X29,X25)
        | esk7_3(X24,X25,X26) != k4_tarski(X28,X29)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk8_3(X24,X25,X26),X24)
        | r2_hidden(esk7_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk9_3(X24,X25,X26),X25)
        | r2_hidden(esk7_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( esk7_3(X24,X25,X26) = k4_tarski(esk8_3(X24,X25,X26),esk9_3(X24,X25,X26))
        | r2_hidden(esk7_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_6,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( X1 = k4_tarski(esk5_4(X2,X3,X4,X1),esk6_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk3_0,esk4_0))
    | X2 != k2_zfmisc_1(X3,X4)
    | ~ r2_hidden(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

fof(c_0_9,plain,(
    ! [X32,X33] :
      ( ( ~ r2_hidden(esk10_2(X32,X33),X32)
        | ~ r2_hidden(esk10_2(X32,X33),X33)
        | X32 = X33 )
      & ( r2_hidden(esk10_2(X32,X33),X32)
        | r2_hidden(esk10_2(X32,X33),X33)
        | X32 = X33 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r2_hidden(esk10_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( k2_zfmisc_1(X1,X2) = X3
    | r2_hidden(esk10_2(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(esk3_0,esk4_0))
    | r2_hidden(esk10_2(k2_zfmisc_1(X1,X2),X3),X3)
    | ~ r2_hidden(esk10_2(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = X1
    | r2_hidden(esk10_2(k2_zfmisc_1(esk1_0,esk2_0),X1),k2_zfmisc_1(esk3_0,esk4_0))
    | r2_hidden(esk10_2(k2_zfmisc_1(esk1_0,esk2_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | X2 != k2_zfmisc_1(X3,X4)
    | ~ r2_hidden(X1,k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_7])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r2_hidden(esk10_2(X1,X2),X1)
    | ~ r2_hidden(esk10_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk10_2(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_14]),c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( X1 = k2_zfmisc_1(esk3_0,esk4_0)
    | r2_hidden(esk10_2(X1,k2_zfmisc_1(esk3_0,esk4_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | r2_hidden(esk10_2(X1,k2_zfmisc_1(esk3_0,esk4_0)),X1)
    | X2 != k2_zfmisc_1(X3,X4)
    | ~ r2_hidden(esk10_2(X1,k2_zfmisc_1(esk3_0,esk4_0)),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(esk10_2(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) != k2_zfmisc_1(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_18]),c_0_15]),c_0_20])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(er,[status(thm)],[c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
