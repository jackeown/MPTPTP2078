%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0712+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:04 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 776 expanded)
%              Number of clauses        :   64 ( 368 expanded)
%              Number of leaves         :    8 ( 183 expanded)
%              Depth                    :   29
%              Number of atoms          :  276 (3127 expanded)
%              Number of equality atoms :   55 ( 474 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(t167_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k2_relat_1(k7_relat_1(X2,k1_tarski(X1))),k1_tarski(k1_funct_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t70_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(c_0_8,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | r1_tarski(k1_relat_1(k7_relat_1(X36,X35)),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => r1_tarski(k2_relat_1(k7_relat_1(X2,k1_tarski(X1))),k1_tarski(k1_funct_1(X2,X1))) ) ),
    inference(assume_negation,[status(cth)],[t167_funct_1])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & ~ r1_tarski(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))),k1_tarski(k1_funct_1(esk7_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3)
    | r2_hidden(esk2_2(k1_relat_1(k7_relat_1(X1,X2)),X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk7_0,X1)),X2)
    | r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk7_0,X1)),X2),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X18,X19,X20,X22,X23,X24,X26] :
      ( ( r2_hidden(esk3_3(X18,X19,X20),k1_relat_1(X18))
        | ~ r2_hidden(X20,X19)
        | X19 != k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( X20 = k1_funct_1(X18,esk3_3(X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(X23,k1_relat_1(X18))
        | X22 != k1_funct_1(X18,X23)
        | r2_hidden(X22,X19)
        | X19 != k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(esk4_2(X18,X24),X24)
        | ~ r2_hidden(X26,k1_relat_1(X18))
        | esk4_2(X18,X24) != k1_funct_1(X18,X26)
        | X24 = k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r2_hidden(esk5_2(X18,X24),k1_relat_1(X18))
        | r2_hidden(esk4_2(X18,X24),X24)
        | X24 = k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( esk4_2(X18,X24) = k1_funct_1(X18,esk5_2(X18,X24))
        | r2_hidden(esk4_2(X18,X24),X24)
        | X24 = k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk7_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( esk2_2(k1_tarski(X1),X2) = X1
    | r1_tarski(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk7_0,X2))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_24])).

cnf(c_0_28,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_3(k7_relat_1(esk7_0,X1),k2_relat_1(k7_relat_1(esk7_0,X1)),X2),X1)
    | ~ v1_funct_1(k7_relat_1(esk7_0,X1))
    | ~ v1_relat_1(k7_relat_1(esk7_0,X1))
    | ~ r2_hidden(X2,k2_relat_1(k7_relat_1(esk7_0,X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_tarski(X3))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( esk3_3(k7_relat_1(esk7_0,k1_tarski(X1)),k2_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))),X2) = X1
    | ~ v1_funct_1(k7_relat_1(esk7_0,k1_tarski(X1)))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1)))
    | ~ r2_hidden(X2,k2_relat_1(k7_relat_1(esk7_0,k1_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_30])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | r2_hidden(esk2_2(k1_tarski(X1),X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))))
    | ~ v1_funct_1(k7_relat_1(esk7_0,k1_tarski(X1)))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1)))
    | ~ r2_hidden(X2,k2_relat_1(k7_relat_1(esk7_0,k1_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_32])).

fof(c_0_35,plain,(
    ! [X30,X31] :
      ( ( v1_relat_1(k7_relat_1(X30,X31))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( v1_funct_1(k7_relat_1(X30,X31))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_tarski(esk2_2(X1,X2)),X3)
    | r1_tarski(X1,X2)
    | r2_hidden(esk2_2(k1_tarski(esk2_2(X1,X2)),X3),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))),X2)
    | r2_hidden(X1,k1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))))
    | ~ v1_funct_1(k7_relat_1(esk7_0,k1_tarski(X1)))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_14])).

cnf(c_0_38,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_40,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | v1_relat_1(k7_relat_1(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_tarski(esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( esk2_2(k1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))),X2) = X1
    | r1_tarski(k1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))),X2)
    | r2_hidden(X1,k1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_18])])).

cnf(c_0_44,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k1_tarski(X1),k1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))))
    | r1_tarski(k1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))),k1_tarski(k1_funct_1(esk7_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))),X2)
    | r2_hidden(X1,k1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_18])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_tarski(X1),k1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_50,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ v1_funct_1(X34)
      | ~ r2_hidden(X32,k1_relat_1(k7_relat_1(X34,X33)))
      | k1_funct_1(k7_relat_1(X34,X33),X32) = k1_funct_1(X34,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k1_tarski(esk6_0),k1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))))
    | r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( esk6_0 = X1
    | r1_tarski(k1_tarski(esk6_0),k1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_51])).

cnf(c_0_54,plain,
    ( k1_funct_1(k7_relat_1(X1,X2),esk3_3(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)),X3)) = k1_funct_1(X1,esk3_3(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)),X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k2_relat_1(k7_relat_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_28]),c_0_44]),c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_tarski(esk6_0),k1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))))
    | r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_53]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk7_0,k1_tarski(X1)),X1) = k1_funct_1(esk7_0,X1)
    | ~ v1_funct_1(k7_relat_1(esk7_0,k1_tarski(X1)))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1)))
    | ~ r2_hidden(X2,k2_relat_1(k7_relat_1(esk7_0,k1_tarski(X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_32]),c_0_39]),c_0_18])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_tarski(esk6_0),k1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))) ),
    inference(ef,[status(thm)],[c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk7_0,k1_tarski(X1)),X1) = k1_funct_1(esk7_0,X1)
    | r1_tarski(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))),X2)
    | ~ v1_funct_1(k7_relat_1(esk7_0,k1_tarski(X1)))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_14])).

cnf(c_0_59,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_60,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))))
    | ~ r2_hidden(X1,k1_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk7_0,k1_tarski(X1)),X1) = k1_funct_1(esk7_0,X1)
    | r1_tarski(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))),X2)
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_38]),c_0_39]),c_0_18])])).

cnf(c_0_63,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_60])])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)),X1) = k1_funct_1(esk7_0,X1)
    | ~ r2_hidden(X1,k1_tarski(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_61]),c_0_39]),c_0_18])])).

cnf(c_0_66,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk7_0,k1_tarski(X1)),X1) = k1_funct_1(esk7_0,X1)
    | r1_tarski(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(X1))),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_44]),c_0_18])])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk7_0,k1_tarski(X1)),X1) = X2
    | ~ v1_funct_1(k7_relat_1(esk7_0,k1_tarski(X1)))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(X1)))
    | ~ r2_hidden(X2,k2_relat_1(k7_relat_1(esk7_0,k1_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_32])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))))
    | ~ v1_funct_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_27])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)),esk6_0) = k1_funct_1(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(esk7_0,esk6_0) = k1_funct_1(esk7_0,X1)
    | ~ v1_funct_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(k7_relat_1(esk7_0,k1_tarski(esk6_0)),k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))),X1)) = k1_funct_1(esk7_0,esk6_0)
    | ~ v1_funct_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))
    | ~ r2_hidden(X1,k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_28])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(k7_relat_1(esk7_0,k1_tarski(esk6_0)),k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))),X1)) = X1
    | ~ v1_funct_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))
    | ~ r2_hidden(X1,k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_65]),c_0_30])).

cnf(c_0_73,negated_conjecture,
    ( X1 = k1_funct_1(esk7_0,esk6_0)
    | ~ v1_funct_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))
    | ~ r2_hidden(X1,k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( esk2_2(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))),X1) = k1_funct_1(esk7_0,esk6_0)
    | r1_tarski(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))),X1)
    | ~ v1_funct_1(k7_relat_1(esk7_0,k1_tarski(esk6_0)))
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_14])).

cnf(c_0_75,negated_conjecture,
    ( esk2_2(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))),X1) = k1_funct_1(esk7_0,esk6_0)
    | r1_tarski(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))),X1)
    | ~ v1_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_38]),c_0_39]),c_0_18])])).

cnf(c_0_76,negated_conjecture,
    ( esk2_2(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))),X1) = k1_funct_1(esk7_0,esk6_0)
    | r1_tarski(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_44]),c_0_18])])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk7_0,k1_tarski(esk6_0))),X1)
    | ~ r2_hidden(k1_funct_1(esk7_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_76])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_77])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_78]),c_0_79])]),
    [proof]).

%------------------------------------------------------------------------------
