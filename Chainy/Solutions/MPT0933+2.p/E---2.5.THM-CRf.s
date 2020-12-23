%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0933+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:58 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   14 (  36 expanded)
%              Number of clauses        :    9 (  11 expanded)
%              Number of leaves         :    2 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 ( 153 expanded)
%              Number of equality atoms :   16 (  73 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

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
    ! [X66,X67] :
      ( ~ v1_relat_1(X67)
      | ~ r2_hidden(X66,X67)
      | X66 = k4_tarski(k1_mcart_1(X66),k2_mcart_1(X66)) ) ),
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
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( k1_mcart_1(esk3_0) = k1_mcart_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( k2_mcart_1(esk3_0) = k2_mcart_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])])).

cnf(c_0_12,negated_conjecture,
    ( esk3_0 != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_8]),c_0_9]),c_0_10]),c_0_7])]),c_0_11]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
