%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t45_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:27 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 126 expanded)
%              Number of clauses        :   24 (  60 expanded)
%              Number of leaves         :    5 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  127 ( 577 expanded)
%              Number of equality atoms :   28 ( 163 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t45_xboole_1.p',t45_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t45_xboole_1.p',d3_xboole_0)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t45_xboole_1.p',t2_tarski)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t45_xboole_1.p',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t45_xboole_1.p',d3_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    inference(assume_negation,[status(cth)],[t45_xboole_1])).

fof(c_0_6,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X19 != k2_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X17)
        | r2_hidden(X21,X19)
        | X19 != k2_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k2_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk4_3(X22,X23,X24),X22)
        | ~ r2_hidden(esk4_3(X22,X23,X24),X24)
        | X24 = k2_xboole_0(X22,X23) )
      & ( ~ r2_hidden(esk4_3(X22,X23,X24),X23)
        | ~ r2_hidden(esk4_3(X22,X23,X24),X24)
        | X24 = k2_xboole_0(X22,X23) )
      & ( r2_hidden(esk4_3(X22,X23,X24),X24)
        | r2_hidden(esk4_3(X22,X23,X24),X22)
        | r2_hidden(esk4_3(X22,X23,X24),X23)
        | X24 = k2_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_7,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & esk2_0 != k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X37,X38] :
      ( ( ~ r2_hidden(esk6_2(X37,X38),X37)
        | ~ r2_hidden(esk6_2(X37,X38),X38)
        | X37 = X38 )
      & ( r2_hidden(esk6_2(X37,X38),X37)
        | r2_hidden(esk6_2(X37,X38),X38)
        | X37 = X38 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_9,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( r2_hidden(X29,X26)
        | ~ r2_hidden(X29,X28)
        | X28 != k4_xboole_0(X26,X27) )
      & ( ~ r2_hidden(X29,X27)
        | ~ r2_hidden(X29,X28)
        | X28 != k4_xboole_0(X26,X27) )
      & ( ~ r2_hidden(X30,X26)
        | r2_hidden(X30,X27)
        | r2_hidden(X30,X28)
        | X28 != k4_xboole_0(X26,X27) )
      & ( ~ r2_hidden(esk5_3(X31,X32,X33),X33)
        | ~ r2_hidden(esk5_3(X31,X32,X33),X31)
        | r2_hidden(esk5_3(X31,X32,X33),X32)
        | X33 = k4_xboole_0(X31,X32) )
      & ( r2_hidden(esk5_3(X31,X32,X33),X31)
        | r2_hidden(esk5_3(X31,X32,X33),X33)
        | X33 = k4_xboole_0(X31,X32) )
      & ( ~ r2_hidden(esk5_3(X31,X32,X33),X32)
        | r2_hidden(esk5_3(X31,X32,X33),X33)
        | X33 = k4_xboole_0(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( esk2_0 != k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r2_hidden(esk6_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk6_2(esk2_0,k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))),k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)))
    | r2_hidden(esk6_2(esk2_0,k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))),esk2_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk6_2(esk2_0,k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))),k4_xboole_0(esk2_0,esk1_0))
    | r2_hidden(esk6_2(esk2_0,k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk3_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk3_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r2_hidden(esk6_2(X1,X2),X1)
    | ~ r2_hidden(esk6_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk6_2(esk2_0,k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))),k2_xboole_0(X1,k4_xboole_0(esk2_0,esk1_0)))
    | r2_hidden(esk6_2(esk2_0,k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))),esk1_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk6_2(esk2_0,k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))),esk1_0)
    | r2_hidden(esk6_2(esk2_0,k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk6_2(esk2_0,k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))),esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_11]),c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_2(esk2_0,k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))),X1)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk6_2(esk2_0,k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))),k2_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk6_2(esk2_0,k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_32]),c_0_33])]),c_0_11]),
    [proof]).
%------------------------------------------------------------------------------
