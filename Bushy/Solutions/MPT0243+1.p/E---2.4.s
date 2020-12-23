%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t38_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:06 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  80 expanded)
%              Number of clauses        :   25 (  39 expanded)
%              Number of leaves         :    4 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 338 expanded)
%              Number of equality atoms :   33 ( 105 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t38_zfmisc_1.p',d2_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t38_zfmisc_1.p',d3_tarski)).

fof(t38_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t38_zfmisc_1.p',t38_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t38_zfmisc_1.p',commutativity_k2_tarski)).

fof(c_0_4,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X12
        | X15 = X13
        | X14 != k2_tarski(X12,X13) )
      & ( X16 != X12
        | r2_hidden(X16,X14)
        | X14 != k2_tarski(X12,X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k2_tarski(X12,X13) )
      & ( esk4_3(X17,X18,X19) != X17
        | ~ r2_hidden(esk4_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( esk4_3(X17,X18,X19) != X18
        | ~ r2_hidden(esk4_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( r2_hidden(esk4_3(X17,X18,X19),X19)
        | esk4_3(X17,X18,X19) = X17
        | esk4_3(X17,X18,X19) = X18
        | X19 = k2_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_5,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_6,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r1_tarski(X21,X22)
        | ~ r2_hidden(X23,X21)
        | r2_hidden(X23,X22) )
      & ( r2_hidden(esk5_2(X24,X25),X24)
        | r1_tarski(X24,X25) )
      & ( ~ r2_hidden(esk5_2(X24,X25),X25)
        | r1_tarski(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t38_zfmisc_1])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_7])])).

fof(c_0_14,negated_conjecture,
    ( ( ~ r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0)
      | ~ r2_hidden(esk1_0,esk3_0)
      | ~ r2_hidden(esk2_0,esk3_0) )
    & ( r2_hidden(esk1_0,esk3_0)
      | r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0) )
    & ( r2_hidden(esk2_0,esk3_0)
      | r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( esk5_2(k2_tarski(X1,X2),X3) = X2
    | esk5_2(k2_tarski(X1,X2),X3) = X1
    | r1_tarski(k2_tarski(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( esk5_2(k2_tarski(X1,X2),X3) = X2
    | r1_tarski(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0)
    | ~ r2_hidden(esk1_0,esk3_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( esk5_2(k2_tarski(esk2_0,X1),esk3_0) = X1
    | r1_tarski(k2_tarski(esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_27,plain,(
    ! [X10,X11] : k2_tarski(X10,X11) = k2_tarski(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k2_tarski(esk2_0,X1),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_26])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k2_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_23])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_tarski(X1,esk2_0),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
