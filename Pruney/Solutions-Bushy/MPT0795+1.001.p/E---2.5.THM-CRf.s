%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0795+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:12 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 278 expanded)
%              Number of clauses        :   31 ( 106 expanded)
%              Number of leaves         :    7 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  268 (1372 expanded)
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

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

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
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( k1_relat_1(X8) = k3_relat_1(X6)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( k2_relat_1(X8) = k3_relat_1(X7)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( v2_funct_1(X8)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(X9,k3_relat_1(X6))
        | ~ r2_hidden(k4_tarski(X9,X10),X6)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(X10,k3_relat_1(X6))
        | ~ r2_hidden(k4_tarski(X9,X10),X6)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X8,X9),k1_funct_1(X8,X10)),X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X6)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X11,k3_relat_1(X6))
        | ~ r2_hidden(X12,k3_relat_1(X6))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X8,X11),k1_funct_1(X8,X12)),X7)
        | r2_hidden(k4_tarski(X11,X12),X6)
        | ~ r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | ~ r2_hidden(esk1_3(X6,X7,X8),k3_relat_1(X6))
        | ~ r2_hidden(esk2_3(X6,X7,X8),k3_relat_1(X6))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X8,esk1_3(X6,X7,X8)),k1_funct_1(X8,esk2_3(X6,X7,X8))),X7)
        | k1_relat_1(X8) != k3_relat_1(X6)
        | k2_relat_1(X8) != k3_relat_1(X7)
        | ~ v2_funct_1(X8)
        | r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X8),k3_relat_1(X6))
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | k1_relat_1(X8) != k3_relat_1(X6)
        | k2_relat_1(X8) != k3_relat_1(X7)
        | ~ v2_funct_1(X8)
        | r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),k3_relat_1(X6))
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | k1_relat_1(X8) != k3_relat_1(X6)
        | k2_relat_1(X8) != k3_relat_1(X7)
        | ~ v2_funct_1(X8)
        | r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X8,esk1_3(X6,X7,X8)),k1_funct_1(X8,esk2_3(X6,X7,X8))),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | k1_relat_1(X8) != k3_relat_1(X6)
        | k2_relat_1(X8) != k3_relat_1(X7)
        | ~ v2_funct_1(X8)
        | r3_wellord1(X6,X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_wellord1])])])])])])).

fof(c_0_8,plain,(
    ! [X17,X18,X19] :
      ( ( r2_hidden(X17,k3_relat_1(X19))
        | ~ r2_hidden(k4_tarski(X17,X18),X19)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(X18,k3_relat_1(X19))
        | ~ r2_hidden(k4_tarski(X17,X18),X19)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

fof(c_0_9,plain,(
    ! [X16] :
      ( v1_relat_1(k6_relat_1(X16))
      & v2_funct_1(k6_relat_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_10,plain,(
    ! [X22] :
      ( k1_relat_1(k6_relat_1(X22)) = X22
      & k2_relat_1(k6_relat_1(X22)) = X22 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_11,plain,(
    ! [X15] :
      ( v1_relat_1(k6_relat_1(X15))
      & v1_funct_1(k6_relat_1(X15)) ) ),
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
    ( r2_hidden(esk2_3(X1,X2,X3),k3_relat_1(X1))
    | r3_wellord1(X1,X2,X3)
    | k3_relat_1(X1) != k1_relat_1(X3)
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
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1))))),X2)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1))),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X1)
    | r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))
    | k3_relat_1(X1) != k3_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))
    | r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))
    | k3_relat_1(X1) != k3_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k3_relat_1(X1))
    | r3_wellord1(X1,X2,X3)
    | k3_relat_1(X1) != k1_relat_1(X3)
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
    ! [X20,X21] :
      ( ~ r2_hidden(X20,X21)
      | k1_funct_1(k6_relat_1(X21),X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_1])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk1_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1))))),esk3_0)
    | r2_hidden(k4_tarski(esk1_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1))),esk2_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))),X1)
    | r3_wellord1(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))
    | k3_relat_1(X1) != k3_relat_1(esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ r3_wellord1(esk3_0,esk3_0,k6_relat_1(k3_relat_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))
    | r3_wellord1(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))
    | k3_relat_1(X1) != k3_relat_1(esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_3(X1,X2,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))
    | r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))
    | k3_relat_1(X1) != k3_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])])).

cnf(c_0_35,plain,
    ( r3_wellord1(X1,X2,X3)
    | k3_relat_1(X1) != k1_relat_1(X3)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ r2_hidden(k4_tarski(k1_funct_1(X3,esk1_3(X1,X2,X3)),k1_funct_1(X3,esk2_3(X1,X2,X3))),X2)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
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
    ( r2_hidden(esk1_3(X1,esk3_0,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))
    | r3_wellord1(X1,esk3_0,k6_relat_1(k3_relat_1(X1)))
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
