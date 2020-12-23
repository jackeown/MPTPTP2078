%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t94_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:16 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   15 (  38 expanded)
%              Number of clauses        :   10 (  13 expanded)
%              Number of leaves         :    2 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 ( 157 expanded)
%              Number of equality atoms :   17 (  75 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_mcart_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( ( r2_hidden(X3,X2)
            & r2_hidden(X1,X2)
            & k1_mcart_1(X3) = k1_mcart_1(X1)
            & k2_mcart_1(X3) = k2_mcart_1(X1) )
         => X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t94_mcart_1.p',t94_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t94_mcart_1.p',t23_mcart_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( ( r2_hidden(X3,X2)
              & r2_hidden(X1,X2)
              & k1_mcart_1(X3) = k1_mcart_1(X1)
              & k2_mcart_1(X3) = k2_mcart_1(X1) )
           => X3 = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t94_mcart_1])).

fof(c_0_3,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | ~ r2_hidden(X13,X14)
      | X13 = k4_tarski(k1_mcart_1(X13),k2_mcart_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_4,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r2_hidden(esk3_0,esk2_0)
    & r2_hidden(esk1_0,esk2_0)
    & k1_mcart_1(esk3_0) = k1_mcart_1(esk1_0)
    & k2_mcart_1(esk3_0) = k2_mcart_1(esk1_0)
    & esk3_0 != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( k1_mcart_1(esk3_0) = k1_mcart_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( k2_mcart_1(esk3_0) = k2_mcart_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( esk3_0 != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
