%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t43_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:27 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  48 expanded)
%              Number of clauses        :   18 (  22 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 175 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t43_xboole_1.p',t43_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t43_xboole_1.p',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t43_xboole_1.p',d3_tarski)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t43_xboole_1.p',d3_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k2_xboole_0(X2,X3))
       => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    inference(assume_negation,[status(cth)],[t43_xboole_1])).

fof(c_0_5,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( r2_hidden(X30,X27)
        | ~ r2_hidden(X30,X29)
        | X29 != k4_xboole_0(X27,X28) )
      & ( ~ r2_hidden(X30,X28)
        | ~ r2_hidden(X30,X29)
        | X29 != k4_xboole_0(X27,X28) )
      & ( ~ r2_hidden(X31,X27)
        | r2_hidden(X31,X28)
        | r2_hidden(X31,X29)
        | X29 != k4_xboole_0(X27,X28) )
      & ( ~ r2_hidden(esk6_3(X32,X33,X34),X34)
        | ~ r2_hidden(esk6_3(X32,X33,X34),X32)
        | r2_hidden(esk6_3(X32,X33,X34),X33)
        | X34 = k4_xboole_0(X32,X33) )
      & ( r2_hidden(esk6_3(X32,X33,X34),X32)
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 = k4_xboole_0(X32,X33) )
      & ( ~ r2_hidden(esk6_3(X32,X33,X34),X33)
        | r2_hidden(esk6_3(X32,X33,X34),X34)
        | X34 = k4_xboole_0(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_6,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    & ~ r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk4_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk4_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk4_2(k4_xboole_0(esk1_0,esk2_0),esk3_0),k4_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_13,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X21,X20)
        | r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X20 != k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | r2_hidden(X22,X20)
        | X20 != k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk5_3(X23,X24,X25),X23)
        | ~ r2_hidden(esk5_3(X23,X24,X25),X25)
        | X25 = k2_xboole_0(X23,X24) )
      & ( ~ r2_hidden(esk5_3(X23,X24,X25),X24)
        | ~ r2_hidden(esk5_3(X23,X24,X25),X25)
        | X25 = k2_xboole_0(X23,X24) )
      & ( r2_hidden(esk5_3(X23,X24,X25),X25)
        | r2_hidden(esk5_3(X23,X24,X25),X23)
        | r2_hidden(esk5_3(X23,X24,X25),X24)
        | X25 = k2_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk4_2(k4_xboole_0(esk1_0,esk2_0),esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk4_2(k4_xboole_0(esk1_0,esk2_0),esk3_0),X1)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_2(k4_xboole_0(esk1_0,esk2_0),esk3_0),k2_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk4_2(k4_xboole_0(esk1_0,esk2_0),esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_12])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_2(k4_xboole_0(esk1_0,esk2_0),esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_9]),
    [proof]).
%------------------------------------------------------------------------------
