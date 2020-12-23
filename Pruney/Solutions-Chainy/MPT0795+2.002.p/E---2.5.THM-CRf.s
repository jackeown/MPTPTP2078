%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:58 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 278 expanded)
%              Number of clauses        :   31 ( 106 expanded)
%              Number of leaves         :    7 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  266 (1358 expanded)
%              Number of equality atoms :   43 ( 210 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   90 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
              <=> ( k1_relat_1(X3) = k3_relat_1(X1)
                  & k2_relat_1(X3) = k3_relat_1(X2)
                  & v2_funct_1(X3)
                  & ! [X4,X5] :
                      ( r2_hidden(k4_tarski(X4,X5),X1)
                    <=> ( r2_hidden(X4,k3_relat_1(X1))
                        & r2_hidden(X5,k3_relat_1(X1))
                        & r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(t52_funct_1,axiom,(
    ! [X1] : v2_funct_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t47_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_wellord1)).

fof(t35_funct_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k1_funct_1(k6_relat_1(X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

fof(c_0_7,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20] :
      ( ( k1_relat_1(X16) = k3_relat_1(X14)
        | ~ r3_wellord1(X14,X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( k2_relat_1(X16) = k3_relat_1(X15)
        | ~ r3_wellord1(X14,X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( v2_funct_1(X16)
        | ~ r3_wellord1(X14,X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(X17,k3_relat_1(X14))
        | ~ r2_hidden(k4_tarski(X17,X18),X14)
        | ~ r3_wellord1(X14,X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(X18,k3_relat_1(X14))
        | ~ r2_hidden(k4_tarski(X17,X18),X14)
        | ~ r3_wellord1(X14,X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X16,X17),k1_funct_1(X16,X18)),X15)
        | ~ r2_hidden(k4_tarski(X17,X18),X14)
        | ~ r3_wellord1(X14,X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(X19,k3_relat_1(X14))
        | ~ r2_hidden(X20,k3_relat_1(X14))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X16,X19),k1_funct_1(X16,X20)),X15)
        | r2_hidden(k4_tarski(X19,X20),X14)
        | ~ r3_wellord1(X14,X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X14,X15,X16),esk2_3(X14,X15,X16)),X14)
        | ~ r2_hidden(esk1_3(X14,X15,X16),k3_relat_1(X14))
        | ~ r2_hidden(esk2_3(X14,X15,X16),k3_relat_1(X14))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X16,esk1_3(X14,X15,X16)),k1_funct_1(X16,esk2_3(X14,X15,X16))),X15)
        | k1_relat_1(X16) != k3_relat_1(X14)
        | k2_relat_1(X16) != k3_relat_1(X15)
        | ~ v2_funct_1(X16)
        | r3_wellord1(X14,X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk1_3(X14,X15,X16),k3_relat_1(X14))
        | r2_hidden(k4_tarski(esk1_3(X14,X15,X16),esk2_3(X14,X15,X16)),X14)
        | k1_relat_1(X16) != k3_relat_1(X14)
        | k2_relat_1(X16) != k3_relat_1(X15)
        | ~ v2_funct_1(X16)
        | r3_wellord1(X14,X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk2_3(X14,X15,X16),k3_relat_1(X14))
        | r2_hidden(k4_tarski(esk1_3(X14,X15,X16),esk2_3(X14,X15,X16)),X14)
        | k1_relat_1(X16) != k3_relat_1(X14)
        | k2_relat_1(X16) != k3_relat_1(X15)
        | ~ v2_funct_1(X16)
        | r3_wellord1(X14,X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X16,esk1_3(X14,X15,X16)),k1_funct_1(X16,esk2_3(X14,X15,X16))),X15)
        | r2_hidden(k4_tarski(esk1_3(X14,X15,X16),esk2_3(X14,X15,X16)),X14)
        | k1_relat_1(X16) != k3_relat_1(X14)
        | k2_relat_1(X16) != k3_relat_1(X15)
        | ~ v2_funct_1(X16)
        | r3_wellord1(X14,X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_wellord1])])])])])])).

fof(c_0_8,plain,(
    ! [X6,X7,X8] :
      ( ( r2_hidden(X6,k3_relat_1(X8))
        | ~ r2_hidden(k4_tarski(X6,X7),X8)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(X7,k3_relat_1(X8))
        | ~ r2_hidden(k4_tarski(X6,X7),X8)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

fof(c_0_9,plain,(
    ! [X13] : v2_funct_1(k6_relat_1(X13)) ),
    inference(variable_rename,[status(thm)],[t52_funct_1])).

fof(c_0_10,plain,(
    ! [X9] :
      ( k1_relat_1(k6_relat_1(X9)) = X9
      & k2_relat_1(k6_relat_1(X9)) = X9 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_11,plain,(
    ! [X10] :
      ( v1_relat_1(k6_relat_1(X10))
      & v1_funct_1(k6_relat_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1))) ) ),
    inference(assume_negation,[status(cth)],[t47_wellord1])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k3_relat_1(X1))
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)
    | r3_wellord1(X1,X2,X3)
    | k1_relat_1(X3) != k3_relat_1(X1)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(X1,esk1_3(X2,X3,X1)),k1_funct_1(X1,esk2_3(X2,X3,X1))),X3)
    | r2_hidden(k4_tarski(esk1_3(X2,X3,X1),esk2_3(X2,X3,X1)),X2)
    | r3_wellord1(X2,X3,X1)
    | k1_relat_1(X1) != k3_relat_1(X2)
    | k2_relat_1(X1) != k3_relat_1(X3)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r3_wellord1(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_22,plain,
    ( r3_wellord1(X1,X2,X3)
    | r2_hidden(esk2_3(X1,X2,X3),k3_relat_1(X1))
    | k1_relat_1(X3) != k3_relat_1(X1)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k3_relat_1(X1))
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)
    | r3_wellord1(X1,X2,X3)
    | k1_relat_1(X3) != k3_relat_1(X1)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1))))),X2)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1))),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X1)
    | k3_relat_1(X1) != k3_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))
    | r2_hidden(esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))
    | k3_relat_1(X1) != k3_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])])).

cnf(c_0_28,plain,
    ( r3_wellord1(X1,X2,X3)
    | r2_hidden(esk1_3(X1,X2,X3),k3_relat_1(X1))
    | k1_relat_1(X3) != k3_relat_1(X1)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r3_wellord1(X1,X2,X3)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),k3_relat_1(X1))
    | ~ r2_hidden(esk2_3(X1,X2,X3),k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(k1_funct_1(X3,esk1_3(X1,X2,X3)),k1_funct_1(X3,esk2_3(X1,X2,X3))),X2)
    | k1_relat_1(X3) != k3_relat_1(X1)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_30,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | k1_funct_1(k6_relat_1(X12),X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_1])])).

cnf(c_0_31,negated_conjecture,
    ( r3_wellord1(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))
    | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk1_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1))))),esk3_0)
    | r2_hidden(k4_tarski(esk1_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1))),esk2_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))),X1)
    | k3_relat_1(X1) != k3_relat_1(esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ r3_wellord1(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( r3_wellord1(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))
    | r2_hidden(esk2_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))
    | k3_relat_1(X1) != k3_relat_1(esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_34,plain,
    ( r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))
    | r2_hidden(esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))
    | k3_relat_1(X1) != k3_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])])).

cnf(c_0_35,plain,
    ( r3_wellord1(X1,X2,X3)
    | k1_relat_1(X3) != k3_relat_1(X1)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(k4_tarski(k1_funct_1(X3,esk1_3(X1,X2,X3)),k1_funct_1(X3,esk2_3(X1,X2,X3))),X2)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_29,c_0_14]),c_0_24])).

cnf(c_0_36,plain,
    ( k1_funct_1(k6_relat_1(X2),X1) = X1
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(esk3_0)),esk1_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))),k1_funct_1(k6_relat_1(k3_relat_1(esk3_0)),esk2_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))))),esk3_0)
    | r2_hidden(k4_tarski(esk1_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))),esk2_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_26])]),c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))),k3_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_26])]),c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r3_wellord1(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))
    | r2_hidden(esk1_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))
    | k3_relat_1(X1) != k3_relat_1(esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_40,plain,
    ( r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))
    | k3_relat_1(X1) != k3_relat_1(X2)
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X2)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1))),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_17]),c_0_18]),c_0_16]),c_0_19]),c_0_20])])]),c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(esk3_0)),esk1_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))),esk2_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))),esk3_0)
    | r2_hidden(k4_tarski(esk1_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))),esk2_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))),k3_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_26])]),c_0_32])).

cnf(c_0_43,plain,
    ( r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))
    | k3_relat_1(X1) != k3_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1))),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X2)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1))),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))),esk2_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_36]),c_0_42])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_44]),c_0_26])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:59:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S069N
% 0.14/0.38  # and selection function SelectComplexAHPExceptRRHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(d7_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)<=>(((k1_relat_1(X3)=k3_relat_1(X1)&k2_relat_1(X3)=k3_relat_1(X2))&v2_funct_1(X3))&![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X1)<=>((r2_hidden(X4,k3_relat_1(X1))&r2_hidden(X5,k3_relat_1(X1)))&r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_wellord1)).
% 0.14/0.38  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 0.14/0.38  fof(t52_funct_1, axiom, ![X1]:v2_funct_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 0.14/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.14/0.38  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.14/0.38  fof(t47_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_wellord1)).
% 0.14/0.38  fof(t35_funct_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k1_funct_1(k6_relat_1(X2),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_1)).
% 0.14/0.38  fof(c_0_7, plain, ![X14, X15, X16, X17, X18, X19, X20]:(((((k1_relat_1(X16)=k3_relat_1(X14)|~r3_wellord1(X14,X15,X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))|~v1_relat_1(X15)|~v1_relat_1(X14))&(k2_relat_1(X16)=k3_relat_1(X15)|~r3_wellord1(X14,X15,X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))|~v1_relat_1(X15)|~v1_relat_1(X14)))&(v2_funct_1(X16)|~r3_wellord1(X14,X15,X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))|~v1_relat_1(X15)|~v1_relat_1(X14)))&((((r2_hidden(X17,k3_relat_1(X14))|~r2_hidden(k4_tarski(X17,X18),X14)|~r3_wellord1(X14,X15,X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))|~v1_relat_1(X15)|~v1_relat_1(X14))&(r2_hidden(X18,k3_relat_1(X14))|~r2_hidden(k4_tarski(X17,X18),X14)|~r3_wellord1(X14,X15,X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))|~v1_relat_1(X15)|~v1_relat_1(X14)))&(r2_hidden(k4_tarski(k1_funct_1(X16,X17),k1_funct_1(X16,X18)),X15)|~r2_hidden(k4_tarski(X17,X18),X14)|~r3_wellord1(X14,X15,X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))|~v1_relat_1(X15)|~v1_relat_1(X14)))&(~r2_hidden(X19,k3_relat_1(X14))|~r2_hidden(X20,k3_relat_1(X14))|~r2_hidden(k4_tarski(k1_funct_1(X16,X19),k1_funct_1(X16,X20)),X15)|r2_hidden(k4_tarski(X19,X20),X14)|~r3_wellord1(X14,X15,X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))|~v1_relat_1(X15)|~v1_relat_1(X14))))&((~r2_hidden(k4_tarski(esk1_3(X14,X15,X16),esk2_3(X14,X15,X16)),X14)|(~r2_hidden(esk1_3(X14,X15,X16),k3_relat_1(X14))|~r2_hidden(esk2_3(X14,X15,X16),k3_relat_1(X14))|~r2_hidden(k4_tarski(k1_funct_1(X16,esk1_3(X14,X15,X16)),k1_funct_1(X16,esk2_3(X14,X15,X16))),X15))|(k1_relat_1(X16)!=k3_relat_1(X14)|k2_relat_1(X16)!=k3_relat_1(X15)|~v2_funct_1(X16))|r3_wellord1(X14,X15,X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))|~v1_relat_1(X15)|~v1_relat_1(X14))&(((r2_hidden(esk1_3(X14,X15,X16),k3_relat_1(X14))|r2_hidden(k4_tarski(esk1_3(X14,X15,X16),esk2_3(X14,X15,X16)),X14)|(k1_relat_1(X16)!=k3_relat_1(X14)|k2_relat_1(X16)!=k3_relat_1(X15)|~v2_funct_1(X16))|r3_wellord1(X14,X15,X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))|~v1_relat_1(X15)|~v1_relat_1(X14))&(r2_hidden(esk2_3(X14,X15,X16),k3_relat_1(X14))|r2_hidden(k4_tarski(esk1_3(X14,X15,X16),esk2_3(X14,X15,X16)),X14)|(k1_relat_1(X16)!=k3_relat_1(X14)|k2_relat_1(X16)!=k3_relat_1(X15)|~v2_funct_1(X16))|r3_wellord1(X14,X15,X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))|~v1_relat_1(X15)|~v1_relat_1(X14)))&(r2_hidden(k4_tarski(k1_funct_1(X16,esk1_3(X14,X15,X16)),k1_funct_1(X16,esk2_3(X14,X15,X16))),X15)|r2_hidden(k4_tarski(esk1_3(X14,X15,X16),esk2_3(X14,X15,X16)),X14)|(k1_relat_1(X16)!=k3_relat_1(X14)|k2_relat_1(X16)!=k3_relat_1(X15)|~v2_funct_1(X16))|r3_wellord1(X14,X15,X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))|~v1_relat_1(X15)|~v1_relat_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_wellord1])])])])])])).
% 0.14/0.38  fof(c_0_8, plain, ![X6, X7, X8]:((r2_hidden(X6,k3_relat_1(X8))|~r2_hidden(k4_tarski(X6,X7),X8)|~v1_relat_1(X8))&(r2_hidden(X7,k3_relat_1(X8))|~r2_hidden(k4_tarski(X6,X7),X8)|~v1_relat_1(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X13]:v2_funct_1(k6_relat_1(X13)), inference(variable_rename,[status(thm)],[t52_funct_1])).
% 0.14/0.38  fof(c_0_10, plain, ![X9]:(k1_relat_1(k6_relat_1(X9))=X9&k2_relat_1(k6_relat_1(X9))=X9), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.14/0.38  fof(c_0_11, plain, ![X10]:(v1_relat_1(k6_relat_1(X10))&v1_funct_1(k6_relat_1(X10))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.14/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1))))), inference(assume_negation,[status(cth)],[t47_wellord1])).
% 0.14/0.38  cnf(c_0_13, plain, (r2_hidden(esk2_3(X1,X2,X3),k3_relat_1(X1))|r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)|r3_wellord1(X1,X2,X3)|k1_relat_1(X3)!=k3_relat_1(X1)|k2_relat_1(X3)!=k3_relat_1(X2)|~v2_funct_1(X3)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_14, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_15, plain, (r2_hidden(k4_tarski(k1_funct_1(X1,esk1_3(X2,X3,X1)),k1_funct_1(X1,esk2_3(X2,X3,X1))),X3)|r2_hidden(k4_tarski(esk1_3(X2,X3,X1),esk2_3(X2,X3,X1)),X2)|r3_wellord1(X2,X3,X1)|k1_relat_1(X1)!=k3_relat_1(X2)|k2_relat_1(X1)!=k3_relat_1(X3)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_16, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_17, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_18, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_19, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_20, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  fof(c_0_21, negated_conjecture, (v1_relat_1(esk3_0)&~r3_wellord1(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.14/0.38  cnf(c_0_22, plain, (r3_wellord1(X1,X2,X3)|r2_hidden(esk2_3(X1,X2,X3),k3_relat_1(X1))|k1_relat_1(X3)!=k3_relat_1(X1)|k2_relat_1(X3)!=k3_relat_1(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.38  cnf(c_0_23, plain, (r2_hidden(esk1_3(X1,X2,X3),k3_relat_1(X1))|r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)|r3_wellord1(X1,X2,X3)|k1_relat_1(X3)!=k3_relat_1(X1)|k2_relat_1(X3)!=k3_relat_1(X2)|~v2_funct_1(X3)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_24, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_25, plain, (r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))|r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1))))),X2)|r2_hidden(k4_tarski(esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1))),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X1)|k3_relat_1(X1)!=k3_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_27, plain, (r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))|r2_hidden(esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))|k3_relat_1(X1)!=k3_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])])).
% 0.14/0.38  cnf(c_0_28, plain, (r3_wellord1(X1,X2,X3)|r2_hidden(esk1_3(X1,X2,X3),k3_relat_1(X1))|k1_relat_1(X3)!=k3_relat_1(X1)|k2_relat_1(X3)!=k3_relat_1(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.38  cnf(c_0_29, plain, (r3_wellord1(X1,X2,X3)|~r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)|~r2_hidden(esk1_3(X1,X2,X3),k3_relat_1(X1))|~r2_hidden(esk2_3(X1,X2,X3),k3_relat_1(X1))|~r2_hidden(k4_tarski(k1_funct_1(X3,esk1_3(X1,X2,X3)),k1_funct_1(X3,esk2_3(X1,X2,X3))),X2)|k1_relat_1(X3)!=k3_relat_1(X1)|k2_relat_1(X3)!=k3_relat_1(X2)|~v2_funct_1(X3)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  fof(c_0_30, plain, ![X11, X12]:(~r2_hidden(X11,X12)|k1_funct_1(k6_relat_1(X12),X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_1])])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (r3_wellord1(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))|r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk1_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1))))),esk3_0)|r2_hidden(k4_tarski(esk1_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1))),esk2_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))),X1)|k3_relat_1(X1)!=k3_relat_1(esk3_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (~r3_wellord1(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (r3_wellord1(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))|r2_hidden(esk2_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))|k3_relat_1(X1)!=k3_relat_1(esk3_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.14/0.38  cnf(c_0_34, plain, (r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))|r2_hidden(esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))|k3_relat_1(X1)!=k3_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])])).
% 0.14/0.38  cnf(c_0_35, plain, (r3_wellord1(X1,X2,X3)|k1_relat_1(X3)!=k3_relat_1(X1)|k2_relat_1(X3)!=k3_relat_1(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~r2_hidden(k4_tarski(k1_funct_1(X3,esk1_3(X1,X2,X3)),k1_funct_1(X3,esk2_3(X1,X2,X3))),X2)|~r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_29, c_0_14]), c_0_24])).
% 0.14/0.38  cnf(c_0_36, plain, (k1_funct_1(k6_relat_1(X2),X1)=X1|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(esk3_0)),esk1_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))),k1_funct_1(k6_relat_1(k3_relat_1(esk3_0)),esk2_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))))),esk3_0)|r2_hidden(k4_tarski(esk1_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))),esk2_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_31]), c_0_26])]), c_0_32])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))),k3_relat_1(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]), c_0_26])]), c_0_32])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (r3_wellord1(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))|r2_hidden(esk1_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))|k3_relat_1(X1)!=k3_relat_1(esk3_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 0.14/0.38  cnf(c_0_40, plain, (r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))|k3_relat_1(X1)!=k3_relat_1(X2)|~r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X2)|~r2_hidden(k4_tarski(esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1))),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_17]), c_0_18]), c_0_16]), c_0_19]), c_0_20])])]), c_0_14])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(esk3_0)),esk1_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))),esk2_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))),esk3_0)|r2_hidden(k4_tarski(esk1_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))),esk2_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_36]), c_0_38])])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))),k3_relat_1(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_39]), c_0_26])]), c_0_32])).
% 0.14/0.38  cnf(c_0_43, plain, (r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))|k3_relat_1(X1)!=k3_relat_1(X2)|~r2_hidden(k4_tarski(esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1))),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X2)|~r2_hidden(k4_tarski(esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1))),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_24])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(esk1_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))),esk2_3(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0)))),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_36]), c_0_42])])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_44]), c_0_26])]), c_0_32]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 46
% 0.14/0.38  # Proof object clause steps            : 31
% 0.14/0.38  # Proof object formula steps           : 15
% 0.14/0.38  # Proof object conjectures             : 14
% 0.14/0.38  # Proof object clause conjectures      : 11
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 14
% 0.14/0.38  # Proof object initial formulas used   : 7
% 0.14/0.38  # Proof object generating inferences   : 14
% 0.14/0.38  # Proof object simplifying inferences  : 48
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 7
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 21
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 21
% 0.14/0.38  # Processed clauses                    : 72
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 3
% 0.14/0.38  # ...remaining for further processing  : 69
% 0.14/0.38  # Other redundant clauses eliminated   : 5
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 2
% 0.14/0.38  # Backward-rewritten                   : 2
% 0.14/0.38  # Generated clauses                    : 68
% 0.14/0.38  # ...of the previous two non-trivial   : 51
% 0.14/0.38  # Contextual simplify-reflections      : 7
% 0.14/0.38  # Paramodulations                      : 58
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 10
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 46
% 0.14/0.38  #    Positive orientable unit clauses  : 9
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 36
% 0.14/0.38  # Current number of unprocessed clauses: 18
% 0.14/0.38  # ...number of literals in the above   : 111
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 23
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 373
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 65
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.14/0.38  # Unit Clause-clause subsumption calls : 8
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 5175
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.031 s
% 0.14/0.38  # System time              : 0.007 s
% 0.14/0.38  # Total time               : 0.038 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
