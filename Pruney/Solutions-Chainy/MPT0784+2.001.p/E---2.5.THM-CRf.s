%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:55 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 423 expanded)
%              Number of clauses        :   53 ( 181 expanded)
%              Number of leaves         :   10 ( 100 expanded)
%              Depth                    :   25
%              Number of atoms          :  323 (1894 expanded)
%              Number of equality atoms :   53 ( 262 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(t33_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( v2_wellord1(X3)
       => r3_xboole_0(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(l4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> ! [X2,X3] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r2_hidden(X3,k3_relat_1(X1))
              & X2 != X3
              & ~ r2_hidden(k4_tarski(X2,X3),X1)
              & ~ r2_hidden(k4_tarski(X3,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(l2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> ! [X2,X3,X4] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X4),X1) )
           => r2_hidden(k4_tarski(X2,X4),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X2),X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(c_0_10,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24] :
      ( ( X21 != X19
        | ~ r2_hidden(X21,X20)
        | X20 != k1_wellord1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(X21,X19),X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k1_wellord1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( X22 = X19
        | ~ r2_hidden(k4_tarski(X22,X19),X18)
        | r2_hidden(X22,X20)
        | X20 != k1_wellord1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(esk2_3(X18,X23,X24),X24)
        | esk2_3(X18,X23,X24) = X23
        | ~ r2_hidden(k4_tarski(esk2_3(X18,X23,X24),X23),X18)
        | X24 = k1_wellord1(X18,X23)
        | ~ v1_relat_1(X18) )
      & ( esk2_3(X18,X23,X24) != X23
        | r2_hidden(esk2_3(X18,X23,X24),X24)
        | X24 = k1_wellord1(X18,X23)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk2_3(X18,X23,X24),X23),X18)
        | r2_hidden(esk2_3(X18,X23,X24),X24)
        | X24 = k1_wellord1(X18,X23)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

fof(c_0_11,plain,(
    ! [X15,X16,X17] :
      ( ( r2_hidden(X15,k3_relat_1(X17))
        | ~ r2_hidden(k4_tarski(X15,X16),X17)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(X16,k3_relat_1(X17))
        | ~ r2_hidden(k4_tarski(X15,X16),X17)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( v2_wellord1(X3)
         => r3_xboole_0(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t33_wellord1])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & v2_wellord1(esk12_0)
    & ~ r3_xboole_0(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_18,plain,(
    ! [X13,X14] :
      ( ( ~ r3_xboole_0(X13,X14)
        | r1_tarski(X13,X14)
        | r1_tarski(X14,X13) )
      & ( ~ r1_tarski(X13,X14)
        | r3_xboole_0(X13,X14) )
      & ( ~ r1_tarski(X14,X13)
        | r3_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_wellord1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ r3_xboole_0(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | r1_tarski(k1_wellord1(X2,X1),X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X26] :
      ( ( v1_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v8_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v4_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v6_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v1_wellord1(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( ~ v1_relat_2(X26)
        | ~ v8_relat_2(X26)
        | ~ v4_relat_2(X26)
        | ~ v6_relat_2(X26)
        | ~ v1_wellord1(X26)
        | v2_wellord1(X26)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_26,plain,(
    ! [X39,X40,X41] :
      ( ( ~ v6_relat_2(X39)
        | ~ r2_hidden(X40,k3_relat_1(X39))
        | ~ r2_hidden(X41,k3_relat_1(X39))
        | X40 = X41
        | r2_hidden(k4_tarski(X40,X41),X39)
        | r2_hidden(k4_tarski(X41,X40),X39)
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(esk8_1(X39),k3_relat_1(X39))
        | v6_relat_2(X39)
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(esk9_1(X39),k3_relat_1(X39))
        | v6_relat_2(X39)
        | ~ v1_relat_1(X39) )
      & ( esk8_1(X39) != esk9_1(X39)
        | v6_relat_2(X39)
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(k4_tarski(esk8_1(X39),esk9_1(X39)),X39)
        | v6_relat_2(X39)
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(k4_tarski(esk9_1(X39),esk8_1(X39)),X39)
        | v6_relat_2(X39)
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk12_0,esk11_0),k1_wellord1(esk12_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk12_0))
    | r1_tarski(k1_wellord1(esk12_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v2_wellord1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( r3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk11_0,k3_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v6_relat_2(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_24])])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

cnf(c_0_36,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( X1 = esk11_0
    | r2_hidden(k4_tarski(X1,esk11_0),esk12_0)
    | r2_hidden(k4_tarski(esk11_0,X1),esk12_0)
    | ~ r2_hidden(X1,k3_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_24])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk10_0,k3_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28])).

fof(c_0_39,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ v8_relat_2(X27)
        | ~ r2_hidden(k4_tarski(X28,X29),X27)
        | ~ r2_hidden(k4_tarski(X29,X30),X27)
        | r2_hidden(k4_tarski(X28,X30),X27)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk3_1(X27),esk4_1(X27)),X27)
        | v8_relat_2(X27)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk4_1(X27),esk5_1(X27)),X27)
        | v8_relat_2(X27)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X27),esk5_1(X27)),X27)
        | v8_relat_2(X27)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).

cnf(c_0_40,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(k4_tarski(esk11_0,esk10_0),esk12_0)
    | r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(X2,X4),X1)
    | ~ v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)
    | r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24])])).

cnf(c_0_45,negated_conjecture,
    ( v8_relat_2(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_30]),c_0_24])])).

cnf(c_0_46,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))
    | r2_hidden(k4_tarski(X1,esk11_0),esk12_0)
    | ~ r2_hidden(k4_tarski(X1,esk10_0),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_24])])).

cnf(c_0_47,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))
    | r2_hidden(k4_tarski(X1,esk11_0),esk12_0)
    | ~ r2_hidden(X1,k1_wellord1(esk12_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_15]),c_0_24])])).

cnf(c_0_48,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(k4_tarski(esk1_2(k1_wellord1(esk12_0,esk10_0),X1),esk11_0),esk12_0)
    | r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))
    | r1_tarski(k1_wellord1(esk12_0,esk10_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_20])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_50,negated_conjecture,
    ( esk1_2(k1_wellord1(esk12_0,esk10_0),X1) = esk11_0
    | esk11_0 = esk10_0
    | r2_hidden(esk1_2(k1_wellord1(esk12_0,esk10_0),X1),k1_wellord1(esk12_0,esk11_0))
    | r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))
    | r1_tarski(k1_wellord1(esk12_0,esk10_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_48]),c_0_24])])).

cnf(c_0_51,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( esk1_2(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) = esk11_0
    | esk11_0 = esk10_0
    | r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_35])).

fof(c_0_53,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(X1,k1_wellord1(X4,X2))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_52]),c_0_35])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(k4_tarski(esk11_0,esk10_0),X1)
    | ~ r1_tarski(esk12_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_24])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(k4_tarski(esk11_0,esk10_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(k4_tarski(X1,esk10_0),esk12_0)
    | ~ r2_hidden(k4_tarski(X1,esk11_0),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_59]),c_0_45]),c_0_24])])).

fof(c_0_61,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v4_relat_2(X34)
        | ~ r2_hidden(k4_tarski(X35,X36),X34)
        | ~ r2_hidden(k4_tarski(X36,X35),X34)
        | X35 = X36
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(k4_tarski(esk6_1(X34),esk7_1(X34)),X34)
        | v4_relat_2(X34)
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(k4_tarski(esk7_1(X34),esk6_1(X34)),X34)
        | v4_relat_2(X34)
        | ~ v1_relat_1(X34) )
      & ( esk6_1(X34) != esk7_1(X34)
        | v4_relat_2(X34)
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).

cnf(c_0_62,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(k4_tarski(X1,esk10_0),esk12_0)
    | ~ r2_hidden(X1,k1_wellord1(esk12_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_15]),c_0_24])])).

cnf(c_0_63,plain,
    ( X2 = X3
    | ~ v4_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(k4_tarski(esk1_2(k1_wellord1(esk12_0,esk11_0),X1),esk10_0),esk12_0)
    | r1_tarski(k1_wellord1(esk12_0,esk11_0),X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_20])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ v4_relat_2(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,k1_wellord1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_15])).

cnf(c_0_66,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_67,negated_conjecture,
    ( esk1_2(k1_wellord1(esk12_0,esk11_0),X1) = esk10_0
    | esk11_0 = esk10_0
    | r2_hidden(esk1_2(k1_wellord1(esk12_0,esk11_0),X1),k1_wellord1(esk12_0,esk10_0))
    | r1_tarski(k1_wellord1(esk12_0,esk11_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_64]),c_0_24])])).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ v4_relat_2(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,k1_wellord1(X3,X1))
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( v4_relat_2(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_30]),c_0_24])])).

cnf(c_0_70,negated_conjecture,
    ( esk1_2(k1_wellord1(esk12_0,esk11_0),k1_wellord1(esk12_0,esk10_0)) = esk10_0
    | esk11_0 = esk10_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_67]),c_0_27])).

cnf(c_0_71,negated_conjecture,
    ( esk11_0 = esk10_0
    | ~ r2_hidden(esk10_0,k1_wellord1(esk12_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_55]),c_0_69]),c_0_24])])).

cnf(c_0_72,negated_conjecture,
    ( esk11_0 = esk10_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_70]),c_0_27]),c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_72]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.030 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 0.21/0.40  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 0.21/0.40  fof(t33_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(v2_wellord1(X3)=>r3_xboole_0(k1_wellord1(X3,X1),k1_wellord1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord1)).
% 0.21/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.40  fof(d9_xboole_0, axiom, ![X1, X2]:(r3_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)|r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_xboole_0)).
% 0.21/0.40  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 0.21/0.40  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 0.21/0.40  fof(l2_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v8_relat_2(X1)<=>![X2, X3, X4]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X4),X1))=>r2_hidden(k4_tarski(X2,X4),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l2_wellord1)).
% 0.21/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.40  fof(l3_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v4_relat_2(X1)<=>![X2, X3]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X2),X1))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_wellord1)).
% 0.21/0.40  fof(c_0_10, plain, ![X18, X19, X20, X21, X22, X23, X24]:((((X21!=X19|~r2_hidden(X21,X20)|X20!=k1_wellord1(X18,X19)|~v1_relat_1(X18))&(r2_hidden(k4_tarski(X21,X19),X18)|~r2_hidden(X21,X20)|X20!=k1_wellord1(X18,X19)|~v1_relat_1(X18)))&(X22=X19|~r2_hidden(k4_tarski(X22,X19),X18)|r2_hidden(X22,X20)|X20!=k1_wellord1(X18,X19)|~v1_relat_1(X18)))&((~r2_hidden(esk2_3(X18,X23,X24),X24)|(esk2_3(X18,X23,X24)=X23|~r2_hidden(k4_tarski(esk2_3(X18,X23,X24),X23),X18))|X24=k1_wellord1(X18,X23)|~v1_relat_1(X18))&((esk2_3(X18,X23,X24)!=X23|r2_hidden(esk2_3(X18,X23,X24),X24)|X24=k1_wellord1(X18,X23)|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk2_3(X18,X23,X24),X23),X18)|r2_hidden(esk2_3(X18,X23,X24),X24)|X24=k1_wellord1(X18,X23)|~v1_relat_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.21/0.40  fof(c_0_11, plain, ![X15, X16, X17]:((r2_hidden(X15,k3_relat_1(X17))|~r2_hidden(k4_tarski(X15,X16),X17)|~v1_relat_1(X17))&(r2_hidden(X16,k3_relat_1(X17))|~r2_hidden(k4_tarski(X15,X16),X17)|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.21/0.40  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(v2_wellord1(X3)=>r3_xboole_0(k1_wellord1(X3,X1),k1_wellord1(X3,X2))))), inference(assume_negation,[status(cth)],[t33_wellord1])).
% 0.21/0.40  cnf(c_0_14, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_12])).
% 0.21/0.40  fof(c_0_16, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.40  fof(c_0_17, negated_conjecture, (v1_relat_1(esk12_0)&(v2_wellord1(esk12_0)&~r3_xboole_0(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.21/0.40  fof(c_0_18, plain, ![X13, X14]:((~r3_xboole_0(X13,X14)|(r1_tarski(X13,X14)|r1_tarski(X14,X13)))&((~r1_tarski(X13,X14)|r3_xboole_0(X13,X14))&(~r1_tarski(X14,X13)|r3_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).
% 0.21/0.40  cnf(c_0_19, plain, (r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X3,k1_wellord1(X2,X1))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.40  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_21, negated_conjecture, (~r3_xboole_0(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  cnf(c_0_22, plain, (r3_xboole_0(X2,X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.40  cnf(c_0_23, plain, (r2_hidden(X1,k3_relat_1(X2))|r1_tarski(k1_wellord1(X2,X1),X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.40  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  fof(c_0_25, plain, ![X26]:((((((v1_relat_2(X26)|~v2_wellord1(X26)|~v1_relat_1(X26))&(v8_relat_2(X26)|~v2_wellord1(X26)|~v1_relat_1(X26)))&(v4_relat_2(X26)|~v2_wellord1(X26)|~v1_relat_1(X26)))&(v6_relat_2(X26)|~v2_wellord1(X26)|~v1_relat_1(X26)))&(v1_wellord1(X26)|~v2_wellord1(X26)|~v1_relat_1(X26)))&(~v1_relat_2(X26)|~v8_relat_2(X26)|~v4_relat_2(X26)|~v6_relat_2(X26)|~v1_wellord1(X26)|v2_wellord1(X26)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.21/0.40  fof(c_0_26, plain, ![X39, X40, X41]:((~v6_relat_2(X39)|(~r2_hidden(X40,k3_relat_1(X39))|~r2_hidden(X41,k3_relat_1(X39))|X40=X41|r2_hidden(k4_tarski(X40,X41),X39)|r2_hidden(k4_tarski(X41,X40),X39))|~v1_relat_1(X39))&(((((r2_hidden(esk8_1(X39),k3_relat_1(X39))|v6_relat_2(X39)|~v1_relat_1(X39))&(r2_hidden(esk9_1(X39),k3_relat_1(X39))|v6_relat_2(X39)|~v1_relat_1(X39)))&(esk8_1(X39)!=esk9_1(X39)|v6_relat_2(X39)|~v1_relat_1(X39)))&(~r2_hidden(k4_tarski(esk8_1(X39),esk9_1(X39)),X39)|v6_relat_2(X39)|~v1_relat_1(X39)))&(~r2_hidden(k4_tarski(esk9_1(X39),esk8_1(X39)),X39)|v6_relat_2(X39)|~v1_relat_1(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.21/0.40  cnf(c_0_27, negated_conjecture, (~r1_tarski(k1_wellord1(esk12_0,esk11_0),k1_wellord1(esk12_0,esk10_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.40  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk12_0))|r1_tarski(k1_wellord1(esk12_0,X1),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.40  cnf(c_0_29, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.40  cnf(c_0_30, negated_conjecture, (v2_wellord1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  cnf(c_0_31, plain, (r3_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.40  cnf(c_0_32, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.40  cnf(c_0_33, negated_conjecture, (r2_hidden(esk11_0,k3_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.40  cnf(c_0_34, negated_conjecture, (v6_relat_2(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_24])])).
% 0.21/0.40  cnf(c_0_35, negated_conjecture, (~r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0))), inference(spm,[status(thm)],[c_0_21, c_0_31])).
% 0.21/0.40  cnf(c_0_36, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  cnf(c_0_37, negated_conjecture, (X1=esk11_0|r2_hidden(k4_tarski(X1,esk11_0),esk12_0)|r2_hidden(k4_tarski(esk11_0,X1),esk12_0)|~r2_hidden(X1,k3_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_24])])).
% 0.21/0.40  cnf(c_0_38, negated_conjecture, (r2_hidden(esk10_0,k3_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_35, c_0_28])).
% 0.21/0.40  fof(c_0_39, plain, ![X27, X28, X29, X30]:((~v8_relat_2(X27)|(~r2_hidden(k4_tarski(X28,X29),X27)|~r2_hidden(k4_tarski(X29,X30),X27)|r2_hidden(k4_tarski(X28,X30),X27))|~v1_relat_1(X27))&(((r2_hidden(k4_tarski(esk3_1(X27),esk4_1(X27)),X27)|v8_relat_2(X27)|~v1_relat_1(X27))&(r2_hidden(k4_tarski(esk4_1(X27),esk5_1(X27)),X27)|v8_relat_2(X27)|~v1_relat_1(X27)))&(~r2_hidden(k4_tarski(esk3_1(X27),esk5_1(X27)),X27)|v8_relat_2(X27)|~v1_relat_1(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).
% 0.21/0.40  cnf(c_0_40, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(er,[status(thm)],[c_0_36])).
% 0.21/0.40  cnf(c_0_41, negated_conjecture, (esk11_0=esk10_0|r2_hidden(k4_tarski(esk11_0,esk10_0),esk12_0)|r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.40  cnf(c_0_42, plain, (v8_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.40  cnf(c_0_43, plain, (r2_hidden(k4_tarski(X2,X4),X1)|~v8_relat_2(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.40  cnf(c_0_44, negated_conjecture, (esk11_0=esk10_0|r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)|r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_24])])).
% 0.21/0.40  cnf(c_0_45, negated_conjecture, (v8_relat_2(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_30]), c_0_24])])).
% 0.21/0.40  cnf(c_0_46, negated_conjecture, (esk11_0=esk10_0|r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))|r2_hidden(k4_tarski(X1,esk11_0),esk12_0)|~r2_hidden(k4_tarski(X1,esk10_0),esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_24])])).
% 0.21/0.40  cnf(c_0_47, negated_conjecture, (esk11_0=esk10_0|r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))|r2_hidden(k4_tarski(X1,esk11_0),esk12_0)|~r2_hidden(X1,k1_wellord1(esk12_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_15]), c_0_24])])).
% 0.21/0.40  cnf(c_0_48, negated_conjecture, (esk11_0=esk10_0|r2_hidden(k4_tarski(esk1_2(k1_wellord1(esk12_0,esk10_0),X1),esk11_0),esk12_0)|r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))|r1_tarski(k1_wellord1(esk12_0,esk10_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_20])).
% 0.21/0.40  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_50, negated_conjecture, (esk1_2(k1_wellord1(esk12_0,esk10_0),X1)=esk11_0|esk11_0=esk10_0|r2_hidden(esk1_2(k1_wellord1(esk12_0,esk10_0),X1),k1_wellord1(esk12_0,esk11_0))|r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))|r1_tarski(k1_wellord1(esk12_0,esk10_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_48]), c_0_24])])).
% 0.21/0.40  cnf(c_0_51, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_52, negated_conjecture, (esk1_2(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0))=esk11_0|esk11_0=esk10_0|r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_35])).
% 0.21/0.40  fof(c_0_53, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.40  cnf(c_0_54, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X4)|~r2_hidden(X1,k1_wellord1(X4,X2))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_51, c_0_15])).
% 0.21/0.40  cnf(c_0_55, negated_conjecture, (esk11_0=esk10_0|r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_52]), c_0_35])).
% 0.21/0.40  cnf(c_0_56, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.40  cnf(c_0_57, negated_conjecture, (esk11_0=esk10_0|r2_hidden(k4_tarski(esk11_0,esk10_0),X1)|~r1_tarski(esk12_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_24])])).
% 0.21/0.40  cnf(c_0_58, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_56])).
% 0.21/0.40  cnf(c_0_59, negated_conjecture, (esk11_0=esk10_0|r2_hidden(k4_tarski(esk11_0,esk10_0),esk12_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.40  cnf(c_0_60, negated_conjecture, (esk11_0=esk10_0|r2_hidden(k4_tarski(X1,esk10_0),esk12_0)|~r2_hidden(k4_tarski(X1,esk11_0),esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_59]), c_0_45]), c_0_24])])).
% 0.21/0.40  fof(c_0_61, plain, ![X34, X35, X36]:((~v4_relat_2(X34)|(~r2_hidden(k4_tarski(X35,X36),X34)|~r2_hidden(k4_tarski(X36,X35),X34)|X35=X36)|~v1_relat_1(X34))&(((r2_hidden(k4_tarski(esk6_1(X34),esk7_1(X34)),X34)|v4_relat_2(X34)|~v1_relat_1(X34))&(r2_hidden(k4_tarski(esk7_1(X34),esk6_1(X34)),X34)|v4_relat_2(X34)|~v1_relat_1(X34)))&(esk6_1(X34)!=esk7_1(X34)|v4_relat_2(X34)|~v1_relat_1(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).
% 0.21/0.40  cnf(c_0_62, negated_conjecture, (esk11_0=esk10_0|r2_hidden(k4_tarski(X1,esk10_0),esk12_0)|~r2_hidden(X1,k1_wellord1(esk12_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_15]), c_0_24])])).
% 0.21/0.40  cnf(c_0_63, plain, (X2=X3|~v4_relat_2(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r2_hidden(k4_tarski(X3,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.40  cnf(c_0_64, negated_conjecture, (esk11_0=esk10_0|r2_hidden(k4_tarski(esk1_2(k1_wellord1(esk12_0,esk11_0),X1),esk10_0),esk12_0)|r1_tarski(k1_wellord1(esk12_0,esk11_0),X1)), inference(spm,[status(thm)],[c_0_62, c_0_20])).
% 0.21/0.40  cnf(c_0_65, plain, (X1=X2|~v4_relat_2(X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,k1_wellord1(X3,X1))), inference(spm,[status(thm)],[c_0_63, c_0_15])).
% 0.21/0.40  cnf(c_0_66, plain, (v4_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.40  cnf(c_0_67, negated_conjecture, (esk1_2(k1_wellord1(esk12_0,esk11_0),X1)=esk10_0|esk11_0=esk10_0|r2_hidden(esk1_2(k1_wellord1(esk12_0,esk11_0),X1),k1_wellord1(esk12_0,esk10_0))|r1_tarski(k1_wellord1(esk12_0,esk11_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_64]), c_0_24])])).
% 0.21/0.40  cnf(c_0_68, plain, (X1=X2|~v4_relat_2(X3)|~v1_relat_1(X3)|~r2_hidden(X2,k1_wellord1(X3,X1))|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(spm,[status(thm)],[c_0_65, c_0_15])).
% 0.21/0.40  cnf(c_0_69, negated_conjecture, (v4_relat_2(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_30]), c_0_24])])).
% 0.21/0.40  cnf(c_0_70, negated_conjecture, (esk1_2(k1_wellord1(esk12_0,esk11_0),k1_wellord1(esk12_0,esk10_0))=esk10_0|esk11_0=esk10_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_67]), c_0_27])).
% 0.21/0.40  cnf(c_0_71, negated_conjecture, (esk11_0=esk10_0|~r2_hidden(esk10_0,k1_wellord1(esk12_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_55]), c_0_69]), c_0_24])])).
% 0.21/0.40  cnf(c_0_72, negated_conjecture, (esk11_0=esk10_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_70]), c_0_27]), c_0_71])).
% 0.21/0.40  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_72]), c_0_58])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 74
% 0.21/0.40  # Proof object clause steps            : 53
% 0.21/0.40  # Proof object formula steps           : 21
% 0.21/0.40  # Proof object conjectures             : 33
% 0.21/0.40  # Proof object clause conjectures      : 30
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 18
% 0.21/0.40  # Proof object initial formulas used   : 10
% 0.21/0.40  # Proof object generating inferences   : 31
% 0.21/0.40  # Proof object simplifying inferences  : 41
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 10
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 40
% 0.21/0.40  # Removed in clause preprocessing      : 0
% 0.21/0.40  # Initial clauses in saturation        : 40
% 0.21/0.40  # Processed clauses                    : 268
% 0.21/0.40  # ...of these trivial                  : 0
% 0.21/0.40  # ...subsumed                          : 63
% 0.21/0.40  # ...remaining for further processing  : 205
% 0.21/0.40  # Other redundant clauses eliminated   : 6
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 48
% 0.21/0.40  # Backward-rewritten                   : 29
% 0.21/0.40  # Generated clauses                    : 468
% 0.21/0.40  # ...of the previous two non-trivial   : 405
% 0.21/0.40  # Contextual simplify-reflections      : 1
% 0.21/0.40  # Paramodulations                      : 461
% 0.21/0.40  # Factorizations                       : 2
% 0.21/0.40  # Equation resolutions                 : 6
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 84
% 0.21/0.40  #    Positive orientable unit clauses  : 11
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 0
% 0.21/0.40  #    Non-unit-clauses                  : 73
% 0.21/0.40  # Current number of unprocessed clauses: 205
% 0.21/0.40  # ...number of literals in the above   : 1081
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 116
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 3480
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 837
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 112
% 0.21/0.40  # Unit Clause-clause subsumption calls : 74
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 1
% 0.21/0.40  # BW rewrite match successes           : 1
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 14112
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.051 s
% 0.21/0.40  # System time              : 0.007 s
% 0.21/0.40  # Total time               : 0.057 s
% 0.21/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
