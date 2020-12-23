%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t184_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:56 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   30 (  99 expanded)
%              Number of clauses        :   21 (  42 expanded)
%              Number of leaves         :    4 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 400 expanded)
%              Number of equality atoms :   23 (  93 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t184_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v3_relat_1(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k2_relat_1(X1))
           => X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t184_relat_1.p',t184_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t184_relat_1.p',d3_tarski)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t184_relat_1.p',d1_tarski)).

fof(d15_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v3_relat_1(X1)
      <=> r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t184_relat_1.p',d15_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( v3_relat_1(X1)
        <=> ! [X2] :
              ( r2_hidden(X2,k2_relat_1(X1))
             => X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t184_relat_1])).

fof(c_0_5,negated_conjecture,(
    ! [X6] :
      ( v1_relat_1(esk1_0)
      & ( r2_hidden(esk2_0,k2_relat_1(esk1_0))
        | ~ v3_relat_1(esk1_0) )
      & ( esk2_0 != k1_xboole_0
        | ~ v3_relat_1(esk1_0) )
      & ( v3_relat_1(esk1_0)
        | ~ r2_hidden(X6,k2_relat_1(esk1_0))
        | X6 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])])).

fof(c_0_6,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( ~ r1_tarski(X17,X18)
        | ~ r2_hidden(X19,X17)
        | r2_hidden(X19,X18) )
      & ( r2_hidden(esk4_2(X20,X21),X20)
        | r1_tarski(X20,X21) )
      & ( ~ r2_hidden(esk4_2(X20,X21),X21)
        | r1_tarski(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,negated_conjecture,
    ( v3_relat_1(esk1_0)
    | X1 = k1_xboole_0
    | ~ r2_hidden(X1,k2_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk3_2(X14,X15),X15)
        | esk3_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk3_2(X14,X15),X15)
        | esk3_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X9] :
      ( ( ~ v3_relat_1(X9)
        | r1_tarski(k2_relat_1(X9),k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(X9) )
      & ( ~ r1_tarski(k2_relat_1(X9),k1_tarski(k1_xboole_0))
        | v3_relat_1(X9)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d15_relat_1])])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( esk4_2(k2_relat_1(esk1_0),X1) = k1_xboole_0
    | r1_tarski(k2_relat_1(esk1_0),X1)
    | v3_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v3_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),X1)
    | v3_relat_1(esk1_0)
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0))
    | ~ v3_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_0,k2_relat_1(esk1_0))
    | ~ v3_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( v3_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_22,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_tarski(k1_xboole_0))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ v3_relat_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk2_0,k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v3_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk2_0,k1_tarski(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21]),c_0_16])])).

cnf(c_0_28,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_21])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
