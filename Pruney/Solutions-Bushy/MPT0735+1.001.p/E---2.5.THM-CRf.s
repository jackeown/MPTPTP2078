%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0735+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:07 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 500 expanded)
%              Number of clauses        :   45 ( 219 expanded)
%              Number of leaves         :    8 ( 126 expanded)
%              Depth                    :   19
%              Number of atoms          :  211 (1855 expanded)
%              Number of equality atoms :   16 (  67 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_ordinal1,conjecture,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(d3_ordinal1,axiom,(
    ! [X1] :
      ( v2_ordinal1(X1)
    <=> ! [X2,X3] :
          ~ ( r2_hidden(X2,X1)
            & r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X3)
            & X2 != X3
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).

fof(t3_ordinal1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & r2_hidden(X2,X3)
        & r2_hidden(X3,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(cc2_ordinal1,axiom,(
    ! [X1] :
      ( ( v1_ordinal1(X1)
        & v2_ordinal1(X1) )
     => v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v3_ordinal1(X2)
       => ( r2_hidden(X1,X2)
         => v3_ordinal1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t23_ordinal1])).

fof(c_0_9,plain,(
    ! [X6] :
      ( ( v1_ordinal1(X6)
        | ~ v3_ordinal1(X6) )
      & ( v2_ordinal1(X6)
        | ~ v3_ordinal1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_10,negated_conjecture,
    ( v3_ordinal1(esk6_0)
    & r2_hidden(esk5_0,esk6_0)
    & ~ v3_ordinal1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(X20,X19) )
      & ( r2_hidden(esk4_2(X21,X22),X21)
        | r1_tarski(X21,X22) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | r1_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_ordinal1(X8)
        | ~ r2_hidden(X9,X8)
        | r1_tarski(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_ordinal1(X10) )
      & ( ~ r1_tarski(esk1_1(X10),X10)
        | v1_ordinal1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_13,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v2_ordinal1(X12)
        | ~ r2_hidden(X13,X12)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X13,X14)
        | X13 = X14
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk2_1(X15),X15)
        | v2_ordinal1(X15) )
      & ( r2_hidden(esk3_1(X15),X15)
        | v2_ordinal1(X15) )
      & ( ~ r2_hidden(esk2_1(X15),esk3_1(X15))
        | v2_ordinal1(X15) )
      & ( esk2_1(X15) != esk3_1(X15)
        | v2_ordinal1(X15) )
      & ( ~ r2_hidden(esk3_1(X15),esk2_1(X15))
        | v2_ordinal1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).

cnf(c_0_14,plain,
    ( v2_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v3_ordinal1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X2,X3)
    | X2 = X3
    | r2_hidden(X3,X2)
    | ~ v2_ordinal1(X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( v2_ordinal1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ r2_hidden(X25,X26)
      | ~ r2_hidden(X26,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_ordinal1])])).

cnf(c_0_24,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(esk5_0,X1)
    | r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk4_2(X1,X2),X3)
    | ~ v1_ordinal1(X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( esk4_2(X1,X2) = esk5_0
    | r1_tarski(X1,X2)
    | r2_hidden(esk4_2(X1,X2),esk5_0)
    | r2_hidden(esk5_0,esk4_2(X1,X2))
    | ~ v1_ordinal1(esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X3,esk4_2(X1,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( esk4_2(X1,esk5_0) = esk5_0
    | r1_tarski(X1,esk5_0)
    | r2_hidden(esk5_0,esk4_2(X1,esk5_0))
    | ~ v1_ordinal1(esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,esk4_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( esk4_2(X1,esk5_0) = esk5_0
    | r1_tarski(X1,esk5_0)
    | ~ v1_ordinal1(esk6_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ v1_ordinal1(esk6_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( v1_ordinal1(esk5_0)
    | ~ v1_ordinal1(esk6_0)
    | ~ r2_hidden(esk1_1(esk5_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_40,plain,
    ( v1_ordinal1(X1)
    | r2_hidden(esk1_1(X1),X2)
    | ~ v1_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_37])).

cnf(c_0_41,plain,
    ( v2_ordinal1(X1)
    | r2_hidden(esk3_1(X1),X2)
    | ~ v1_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_43,plain,(
    ! [X7] :
      ( ~ v1_ordinal1(X7)
      | ~ v2_ordinal1(X7)
      | v3_ordinal1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_ordinal1])])).

cnf(c_0_44,negated_conjecture,
    ( v1_ordinal1(esk5_0)
    | ~ v1_ordinal1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_19])])).

cnf(c_0_45,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_46,plain,
    ( X1 = esk3_1(X2)
    | v2_ordinal1(X2)
    | r2_hidden(esk3_1(X2),X1)
    | r2_hidden(X1,esk3_1(X2))
    | ~ v2_ordinal1(X3)
    | ~ v1_ordinal1(X3)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_41])).

cnf(c_0_47,plain,
    ( v2_ordinal1(X1)
    | r2_hidden(esk2_1(X1),X2)
    | ~ v1_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_42])).

cnf(c_0_48,plain,
    ( v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( v1_ordinal1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_15])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_51,plain,
    ( esk2_1(X1) = esk3_1(X2)
    | v2_ordinal1(X1)
    | v2_ordinal1(X2)
    | r2_hidden(esk2_1(X1),esk3_1(X2))
    | r2_hidden(esk3_1(X2),esk2_1(X1))
    | ~ v2_ordinal1(X3)
    | ~ v1_ordinal1(X3)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_ordinal1(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( esk2_1(X1) = esk3_1(esk5_0)
    | v2_ordinal1(X1)
    | r2_hidden(esk3_1(esk5_0),esk2_1(X1))
    | r2_hidden(esk2_1(X1),esk3_1(esk5_0))
    | ~ v1_ordinal1(esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_19]),c_0_20])]),c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( esk2_1(X1) = esk3_1(esk5_0)
    | v2_ordinal1(X1)
    | r2_hidden(esk2_1(X1),esk3_1(esk5_0))
    | r2_hidden(esk3_1(esk5_0),esk2_1(X1))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_45]),c_0_15])])).

cnf(c_0_55,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk3_1(X1),esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_56,negated_conjecture,
    ( esk3_1(esk5_0) = esk2_1(esk5_0)
    | r2_hidden(esk3_1(esk5_0),esk2_1(esk5_0))
    | r2_hidden(esk2_1(esk5_0),esk3_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_19]),c_0_52])).

cnf(c_0_57,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk2_1(X1),esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( esk3_1(esk5_0) = esk2_1(esk5_0)
    | r2_hidden(esk2_1(esk5_0),esk3_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_52])).

cnf(c_0_59,plain,
    ( v2_ordinal1(X1)
    | esk2_1(X1) != esk3_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_60,negated_conjecture,
    ( esk3_1(esk5_0) = esk2_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_52]),
    [proof]).

%------------------------------------------------------------------------------
