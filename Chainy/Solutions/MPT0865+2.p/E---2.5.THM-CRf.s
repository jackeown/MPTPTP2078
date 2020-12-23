%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0865+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:55 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   18 (  67 expanded)
%              Number of clauses        :   11 (  26 expanded)
%              Number of leaves         :    3 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 ( 167 expanded)
%              Number of equality atoms :   18 (  68 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_mcart_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',d1_relat_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,X2)
         => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t23_mcart_1])).

fof(c_0_4,plain,(
    ! [X173,X174,X177,X179,X180] :
      ( ( ~ v1_relat_1(X173)
        | ~ r2_hidden(X174,X173)
        | X174 = k4_tarski(esk37_2(X173,X174),esk38_2(X173,X174)) )
      & ( r2_hidden(esk39_1(X177),X177)
        | v1_relat_1(X177) )
      & ( esk39_1(X177) != k4_tarski(X179,X180)
        | v1_relat_1(X177) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r2_hidden(esk1_0,esk2_0)
    & esk1_0 != k4_tarski(k1_mcart_1(esk1_0),k2_mcart_1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X416,X417] :
      ( k1_mcart_1(k4_tarski(X416,X417)) = X416
      & k2_mcart_1(k4_tarski(X416,X417)) = X417 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_7,plain,
    ( X2 = k4_tarski(esk37_2(X1,X2),esk38_2(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( k4_tarski(esk37_2(esk2_0,esk1_0),esk38_2(esk2_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_12,negated_conjecture,
    ( esk37_2(esk2_0,esk1_0) = k1_mcart_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk1_0),esk38_2(esk2_0,esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk38_2(esk2_0,esk1_0) = k2_mcart_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( esk1_0 != k4_tarski(k1_mcart_1(esk1_0),k2_mcart_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
