%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0957+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  22 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   68 (  71 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t30_wellord2,conjecture,(
    ! [X1] : r8_relat_2(k1_wellord2(X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord2)).

fof(d16_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> r8_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_2)).

fof(t3_wellord2,axiom,(
    ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).

fof(c_0_5,plain,(
    ! [X6,X7,X8,X9] :
      ( ( k3_relat_1(X7) = X6
        | X7 != k1_wellord2(X6)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X8,X9),X7)
        | r1_tarski(X8,X9)
        | ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X9,X6)
        | X7 != k1_wellord2(X6)
        | ~ v1_relat_1(X7) )
      & ( ~ r1_tarski(X8,X9)
        | r2_hidden(k4_tarski(X8,X9),X7)
        | ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X9,X6)
        | X7 != k1_wellord2(X6)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk1_2(X6,X7),X6)
        | k3_relat_1(X7) != X6
        | X7 = k1_wellord2(X6)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk2_2(X6,X7),X6)
        | k3_relat_1(X7) != X6
        | X7 = k1_wellord2(X6)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X6,X7),esk2_2(X6,X7)),X7)
        | ~ r1_tarski(esk1_2(X6,X7),esk2_2(X6,X7))
        | k3_relat_1(X7) != X6
        | X7 = k1_wellord2(X6)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_2(X6,X7),esk2_2(X6,X7)),X7)
        | r1_tarski(esk1_2(X6,X7),esk2_2(X6,X7))
        | k3_relat_1(X7) != X6
        | X7 = k1_wellord2(X6)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_6,plain,(
    ! [X12] : v1_relat_1(k1_wellord2(X12)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] : r8_relat_2(k1_wellord2(X1),X1) ),
    inference(assume_negation,[status(cth)],[t30_wellord2])).

fof(c_0_8,plain,(
    ! [X5] :
      ( ( ~ v8_relat_2(X5)
        | r8_relat_2(X5,k3_relat_1(X5))
        | ~ v1_relat_1(X5) )
      & ( ~ r8_relat_2(X5,k3_relat_1(X5))
        | v8_relat_2(X5)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_2])])])).

fof(c_0_9,plain,(
    ! [X13] : v8_relat_2(k1_wellord2(X13)) ),
    inference(variable_rename,[status(thm)],[t3_wellord2])).

cnf(c_0_10,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,negated_conjecture,(
    ~ r8_relat_2(k1_wellord2(esk3_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_13,plain,
    ( r8_relat_2(X1,k3_relat_1(X1))
    | ~ v8_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v8_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( ~ r8_relat_2(k1_wellord2(esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r8_relat_2(k1_wellord2(X1),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_11])]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17])]),
    [proof]).

%------------------------------------------------------------------------------
