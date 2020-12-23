%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t31_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:01 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  57 expanded)
%              Number of clauses        :   14 (  20 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 ( 179 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t31_relat_1.p',t31_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t31_relat_1.p',t25_relat_1)).

fof(t13_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t31_relat_1.p',t13_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t31_relat_1.p',d6_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

fof(c_0_5,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(k1_relat_1(X17),k1_relat_1(X18))
        | ~ r1_tarski(X17,X18)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17) )
      & ( r1_tarski(k2_relat_1(X17),k2_relat_1(X18))
        | ~ r1_tarski(X17,X18)
        | ~ v1_relat_1(X18)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,esk2_0)
    & ~ r1_tarski(k3_relat_1(esk1_0),k3_relat_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(k2_xboole_0(X13,X15),k2_xboole_0(X14,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_8,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,k2_relat_1(esk1_0)),k2_xboole_0(X2,k2_relat_1(esk2_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_9]),c_0_10]),c_0_11])])).

fof(c_0_17,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k3_relat_1(X9) = k2_xboole_0(k1_relat_1(X9),k2_relat_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_relat_1(esk1_0),k2_relat_1(esk1_0)),k2_xboole_0(k1_relat_1(esk2_0),k2_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_relat_1(esk1_0),k2_relat_1(esk1_0)),k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_10])])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk1_0),k3_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_11])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
