%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : ordinal1__t23_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:25 EDT 2019

% Result     : Theorem 182.16s
% Output     : CNFRefutation 182.25s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 171 expanded)
%              Number of clauses        :   41 (  72 expanded)
%              Number of leaves         :    8 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  168 ( 636 expanded)
%              Number of equality atoms :    9 (  28 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_ordinal1,conjecture,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',t23_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',d2_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',cc1_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',d3_tarski)).

fof(t3_ordinal1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & r2_hidden(X2,X3)
        & r2_hidden(X3,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',t3_ordinal1)).

fof(d3_ordinal1,axiom,(
    ! [X1] :
      ( v2_ordinal1(X1)
    <=> ! [X2,X3] :
          ~ ( r2_hidden(X2,X1)
            & r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X3)
            & X2 != X3
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',d3_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',antisymmetry_r2_hidden)).

fof(cc2_ordinal1,axiom,(
    ! [X1] :
      ( ( v1_ordinal1(X1)
        & v2_ordinal1(X1) )
     => v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t23_ordinal1.p',cc2_ordinal1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v3_ordinal1(X2)
       => ( r2_hidden(X1,X2)
         => v3_ordinal1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t23_ordinal1])).

fof(c_0_9,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_ordinal1(X9)
        | ~ r2_hidden(X10,X9)
        | r1_tarski(X10,X9) )
      & ( r2_hidden(esk3_1(X11),X11)
        | v1_ordinal1(X11) )
      & ( ~ r1_tarski(esk3_1(X11),X11)
        | v1_ordinal1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_10,negated_conjecture,
    ( v3_ordinal1(esk2_0)
    & r2_hidden(esk1_0,esk2_0)
    & ~ v3_ordinal1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_11,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X66] :
      ( ( v1_ordinal1(X66)
        | ~ v3_ordinal1(X66) )
      & ( v2_ordinal1(X66)
        | ~ v3_ordinal1(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_14,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r1_tarski(X19,X20)
        | ~ r2_hidden(X21,X19)
        | r2_hidden(X21,X20) )
      & ( r2_hidden(esk6_2(X22,X23),X22)
        | r1_tarski(X22,X23) )
      & ( ~ r2_hidden(esk6_2(X22,X23),X23)
        | r1_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    | ~ v1_ordinal1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_21,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( v1_ordinal1(esk1_0)
    | r2_hidden(esk3_1(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk3_1(esk1_0),esk2_0)
    | v1_ordinal1(esk1_0)
    | ~ v1_ordinal1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_22])).

fof(c_0_24,plain,(
    ! [X45,X46,X47] :
      ( ~ r2_hidden(X45,X46)
      | ~ r2_hidden(X46,X47)
      | ~ r2_hidden(X47,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_ordinal1])])).

fof(c_0_25,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ v2_ordinal1(X13)
        | ~ r2_hidden(X14,X13)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X14,X15)
        | X14 = X15
        | r2_hidden(X15,X14) )
      & ( r2_hidden(esk4_1(X16),X16)
        | v2_ordinal1(X16) )
      & ( r2_hidden(esk5_1(X16),X16)
        | v2_ordinal1(X16) )
      & ( ~ r2_hidden(esk4_1(X16),esk5_1(X16))
        | v2_ordinal1(X16) )
      & ( esk4_1(X16) != esk5_1(X16)
        | v2_ordinal1(X16) )
      & ( ~ r2_hidden(esk5_1(X16),esk4_1(X16))
        | v2_ordinal1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).

cnf(c_0_26,plain,
    ( v2_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk3_1(esk1_0),esk2_0)
    | v1_ordinal1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_17])])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X2,X3)
    | X2 = X3
    | r2_hidden(X3,X2)
    | ~ v2_ordinal1(X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v2_ordinal1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( v1_ordinal1(esk1_0)
    | r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( v1_ordinal1(X1)
    | ~ r2_hidden(X2,esk3_1(X1))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

fof(c_0_34,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | ~ r2_hidden(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_35,negated_conjecture,
    ( X1 = esk1_0
    | r2_hidden(X1,esk1_0)
    | r2_hidden(esk1_0,X1)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_12]),c_0_30])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk3_1(esk1_0),X1)
    | v1_ordinal1(esk1_0)
    | r2_hidden(esk6_2(esk3_1(esk1_0),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r1_tarski(esk3_1(X1),X2)
    | v1_ordinal1(X1)
    | ~ r2_hidden(X1,esk6_2(esk3_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk6_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( esk6_2(esk3_1(esk1_0),X1) = esk1_0
    | r1_tarski(esk3_1(esk1_0),X1)
    | v1_ordinal1(esk1_0)
    | r2_hidden(esk6_2(esk3_1(esk1_0),X1),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_42,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_43,negated_conjecture,
    ( v2_ordinal1(esk1_0)
    | r2_hidden(esk5_1(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_38])).

cnf(c_0_44,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_45,plain,(
    ! [X67] :
      ( ~ v1_ordinal1(X67)
      | ~ v2_ordinal1(X67)
      | v3_ordinal1(X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_ordinal1])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,esk6_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( esk6_2(esk3_1(esk1_0),esk1_0) = esk1_0
    | v1_ordinal1(esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( X1 = esk5_1(esk1_0)
    | v2_ordinal1(esk1_0)
    | r2_hidden(X1,esk5_1(esk1_0))
    | r2_hidden(esk5_1(esk1_0),X1)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_43]),c_0_30])])).

cnf(c_0_49,negated_conjecture,
    ( v2_ordinal1(esk1_0)
    | r2_hidden(esk4_1(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_44])).

cnf(c_0_50,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk5_1(X1),esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_51,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk4_1(X1),esk5_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_52,plain,
    ( v2_ordinal1(X1)
    | esk4_1(X1) != esk5_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_53,plain,
    ( v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( v1_ordinal1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_21]),c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( v2_ordinal1(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
