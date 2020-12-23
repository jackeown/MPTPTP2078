%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t73_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:04 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   24 (  55 expanded)
%              Number of clauses        :   15 (  23 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 200 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r2_hidden(k4_tarski(X3,X3),X2) )
       => r1_tarski(k6_relat_1(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t73_relat_1.p',t73_relat_1)).

fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t73_relat_1.p',d10_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t73_relat_1.p',dt_k6_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t73_relat_1.p',d3_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( ! [X3] :
              ( r2_hidden(X3,X1)
             => r2_hidden(k4_tarski(X3,X3),X2) )
         => r1_tarski(k6_relat_1(X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t73_relat_1])).

fof(c_0_5,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X12,X10)
        | ~ r2_hidden(k4_tarski(X12,X13),X11)
        | X11 != k6_relat_1(X10)
        | ~ v1_relat_1(X11) )
      & ( X12 = X13
        | ~ r2_hidden(k4_tarski(X12,X13),X11)
        | X11 != k6_relat_1(X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(X14,X10)
        | X14 != X15
        | r2_hidden(k4_tarski(X14,X15),X11)
        | X11 != k6_relat_1(X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X10,X11),esk4_2(X10,X11)),X11)
        | ~ r2_hidden(esk3_2(X10,X11),X10)
        | esk3_2(X10,X11) != esk4_2(X10,X11)
        | X11 = k6_relat_1(X10)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk3_2(X10,X11),X10)
        | r2_hidden(k4_tarski(esk3_2(X10,X11),esk4_2(X10,X11)),X11)
        | X11 = k6_relat_1(X10)
        | ~ v1_relat_1(X11) )
      & ( esk3_2(X10,X11) = esk4_2(X10,X11)
        | r2_hidden(k4_tarski(esk3_2(X10,X11),esk4_2(X10,X11)),X11)
        | X11 = k6_relat_1(X10)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X25] : v1_relat_1(k6_relat_1(X25)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_7,negated_conjecture,(
    ! [X7] :
      ( v1_relat_1(esk2_0)
      & ( ~ r2_hidden(X7,esk1_0)
        | r2_hidden(k4_tarski(X7,X7),esk2_0) )
      & ~ r1_tarski(k6_relat_1(esk1_0),esk2_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_8,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(k4_tarski(X20,X21),X18)
        | r2_hidden(k4_tarski(X20,X21),X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk5_2(X18,X22),esk6_2(X18,X22)),X18)
        | r1_tarski(X18,X22)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X18,X22),esk6_2(X18,X22)),X22)
        | r1_tarski(X18,X22)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_9,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_tarski(k6_relat_1(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_2(k6_relat_1(esk1_0),esk2_0),esk6_2(k6_relat_1(esk1_0),esk2_0)),k6_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_10])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_2(k6_relat_1(esk1_0),esk2_0),esk6_2(k6_relat_1(esk1_0),esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_13]),c_0_10])])).

cnf(c_0_18,negated_conjecture,
    ( esk6_2(k6_relat_1(esk1_0),esk2_0) = esk5_2(k6_relat_1(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_10])])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_2(k6_relat_1(esk1_0),esk2_0),esk5_2(k6_relat_1(esk1_0),esk2_0)),esk2_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk5_2(k6_relat_1(esk1_0),esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
