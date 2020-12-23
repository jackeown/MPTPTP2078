%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0745+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:08 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 132 expanded)
%              Number of clauses        :   44 (  66 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  226 ( 684 expanded)
%              Number of equality atoms :   18 ( 108 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t35_ordinal1,conjecture,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => v3_ordinal1(X2) )
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

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

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(d4_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
    <=> ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_ordinal1)).

fof(c_0_9,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( ~ r1_tarski(X16,X17)
        | ~ r2_hidden(X18,X16)
        | r2_hidden(X18,X17) )
      & ( r2_hidden(esk4_2(X19,X20),X19)
        | r1_tarski(X19,X20) )
      & ( ~ r2_hidden(esk4_2(X19,X20),X20)
        | r1_tarski(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_ordinal1(X6)
        | ~ r2_hidden(X7,X6)
        | r1_tarski(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_ordinal1(X8) )
      & ( ~ r1_tarski(esk1_1(X8),X8)
        | v1_ordinal1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_11,plain,(
    ! [X23,X24,X25,X27,X28,X29,X30,X32] :
      ( ( r2_hidden(X25,esk5_3(X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k3_tarski(X23) )
      & ( r2_hidden(esk5_3(X23,X24,X25),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k3_tarski(X23) )
      & ( ~ r2_hidden(X27,X28)
        | ~ r2_hidden(X28,X23)
        | r2_hidden(X27,X24)
        | X24 != k3_tarski(X23) )
      & ( ~ r2_hidden(esk6_2(X29,X30),X30)
        | ~ r2_hidden(esk6_2(X29,X30),X32)
        | ~ r2_hidden(X32,X29)
        | X30 = k3_tarski(X29) )
      & ( r2_hidden(esk6_2(X29,X30),esk7_2(X29,X30))
        | r2_hidden(esk6_2(X29,X30),X30)
        | X30 = k3_tarski(X29) )
      & ( r2_hidden(esk7_2(X29,X30),X29)
        | r2_hidden(esk6_2(X29,X30),X30)
        | X30 = k3_tarski(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,esk5_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ v1_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,esk5_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(esk5_3(X3,k3_tarski(X3),X1),X2)
    | ~ r2_hidden(X1,k3_tarski(X3))
    | ~ v1_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(esk5_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_tarski(X2))
    | ~ v1_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k3_tarski(esk5_3(X2,k3_tarski(X2),X3)))
    | ~ r2_hidden(X3,k3_tarski(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

fof(c_0_24,plain,(
    ! [X5] :
      ( ( v1_ordinal1(X5)
        | ~ v3_ordinal1(X5) )
      & ( v2_ordinal1(X5)
        | ~ v3_ordinal1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X1)
           => v3_ordinal1(X2) )
       => v3_ordinal1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t35_ordinal1])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,esk5_3(X2,k3_tarski(X2),X3))
    | ~ r2_hidden(X3,k3_tarski(X2))
    | ~ r2_hidden(X1,X3)
    | ~ v1_ordinal1(esk5_3(X2,k3_tarski(X2),X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,negated_conjecture,(
    ! [X39] :
      ( ( ~ r2_hidden(X39,esk8_0)
        | v3_ordinal1(X39) )
      & ~ v3_ordinal1(k3_tarski(esk8_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])])).

fof(c_0_29,plain,(
    ! [X34,X35] :
      ( ~ v3_ordinal1(X35)
      | ~ r2_hidden(X34,X35)
      | v3_ordinal1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,esk5_3(X2,k3_tarski(X2),X3))
    | ~ r2_hidden(X3,k3_tarski(X2))
    | ~ r2_hidden(X1,X3)
    | ~ v3_ordinal1(esk5_3(X2,k3_tarski(X2),X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,esk5_3(X2,k3_tarski(X2),X3))
    | ~ r2_hidden(esk5_3(X2,k3_tarski(X2),X3),esk8_0)
    | ~ r2_hidden(X3,k3_tarski(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(X2))
    | ~ v3_ordinal1(esk5_3(X2,k3_tarski(X2),X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,esk5_3(X2,k3_tarski(X2),X3))
    | ~ r2_hidden(X3,k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk5_3(esk8_0,k3_tarski(esk8_0),X2))
    | ~ r2_hidden(X2,k3_tarski(esk8_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(esk5_3(X2,k3_tarski(X2),X1),esk8_0)
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

fof(c_0_38,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ v2_ordinal1(X10)
        | ~ r2_hidden(X11,X10)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X11,X12)
        | X11 = X12
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_1(X13),X13)
        | v2_ordinal1(X13) )
      & ( r2_hidden(esk3_1(X13),X13)
        | v2_ordinal1(X13) )
      & ( ~ r2_hidden(esk2_1(X13),esk3_1(X13))
        | v2_ordinal1(X13) )
      & ( esk2_1(X13) != esk3_1(X13)
        | v2_ordinal1(X13) )
      & ( ~ r2_hidden(esk3_1(X13),esk2_1(X13))
        | v2_ordinal1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk8_0))
    | ~ r2_hidden(X2,k3_tarski(esk8_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_41,plain,(
    ! [X36,X37] :
      ( ~ v3_ordinal1(X36)
      | ~ v3_ordinal1(X37)
      | r2_hidden(X36,X37)
      | X36 = X37
      | r2_hidden(X37,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_42,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_43,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk8_0))
    | v1_ordinal1(k3_tarski(esk8_0))
    | ~ r2_hidden(X1,esk1_1(k3_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( v2_ordinal1(k3_tarski(esk8_0))
    | v3_ordinal1(esk3_1(k3_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_49,plain,(
    ! [X22] :
      ( ( v1_ordinal1(X22)
        | ~ v3_ordinal1(X22) )
      & ( v2_ordinal1(X22)
        | ~ v3_ordinal1(X22) )
      & ( ~ v1_ordinal1(X22)
        | ~ v2_ordinal1(X22)
        | v3_ordinal1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_ordinal1])])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk1_1(k3_tarski(esk8_0)),X1)
    | r2_hidden(esk4_2(esk1_1(k3_tarski(esk8_0)),X1),k3_tarski(esk8_0))
    | v1_ordinal1(k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( X1 = esk3_1(k3_tarski(esk8_0))
    | r2_hidden(X1,esk3_1(k3_tarski(esk8_0)))
    | r2_hidden(esk3_1(k3_tarski(esk8_0)),X1)
    | v2_ordinal1(k3_tarski(esk8_0))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v2_ordinal1(k3_tarski(esk8_0))
    | v3_ordinal1(esk2_1(k3_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_48])).

cnf(c_0_55,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk3_1(X1),esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_56,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk2_1(X1),esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_57,plain,
    ( v2_ordinal1(X1)
    | esk2_1(X1) != esk3_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_58,plain,
    ( v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( v1_ordinal1(k3_tarski(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( v2_ordinal1(k3_tarski(esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])]),c_0_61]),
    [proof]).

%------------------------------------------------------------------------------
