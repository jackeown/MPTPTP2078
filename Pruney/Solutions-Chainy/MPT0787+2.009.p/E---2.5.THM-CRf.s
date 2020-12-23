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
% DateTime   : Thu Dec  3 10:56:56 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 (1062 expanded)
%              Number of clauses        :   67 ( 449 expanded)
%              Number of leaves         :   11 ( 249 expanded)
%              Depth                    :   20
%              Number of atoms          :  427 (6428 expanded)
%              Number of equality atoms :   67 ( 920 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   51 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) )
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t36_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ( v2_wellord1(X2)
          & r1_tarski(X1,k3_relat_1(X2)) )
       => ( ~ ( X1 != k3_relat_1(X2)
              & ! [X3] :
                  ~ ( r2_hidden(X3,k3_relat_1(X2))
                    & X1 = k1_wellord1(X2,X3) ) )
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
             => ! [X4] :
                  ( r2_hidden(k4_tarski(X4,X3),X2)
                 => r2_hidden(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).

fof(t13_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(s1_xboole_0__e7_18__wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => ? [X3] :
        ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,k3_relat_1(X1))
            & ~ r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).

fof(t10_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r1_tarski(X2,k3_relat_1(X1))
              & X2 != k1_xboole_0
              & ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) )
         => ( r2_hidden(k4_tarski(X1,X2),X3)
          <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_wellord1])).

fof(c_0_12,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v6_relat_2(X25)
        | ~ r2_hidden(X26,k3_relat_1(X25))
        | ~ r2_hidden(X27,k3_relat_1(X25))
        | X26 = X27
        | r2_hidden(k4_tarski(X26,X27),X25)
        | r2_hidden(k4_tarski(X27,X26),X25)
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(esk3_1(X25),k3_relat_1(X25))
        | v6_relat_2(X25)
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(esk4_1(X25),k3_relat_1(X25))
        | v6_relat_2(X25)
        | ~ v1_relat_1(X25) )
      & ( esk3_1(X25) != esk4_1(X25)
        | v6_relat_2(X25)
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X25),esk4_1(X25)),X25)
        | v6_relat_2(X25)
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(k4_tarski(esk4_1(X25),esk3_1(X25)),X25)
        | v6_relat_2(X25)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & v2_wellord1(esk12_0)
    & r2_hidden(esk10_0,k3_relat_1(esk12_0))
    & r2_hidden(esk11_0,k3_relat_1(esk12_0))
    & ( ~ r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)
      | ~ r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) )
    & ( r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)
      | r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_14,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk11_0,k3_relat_1(esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X24] :
      ( ( v1_relat_2(X24)
        | ~ v2_wellord1(X24)
        | ~ v1_relat_1(X24) )
      & ( v8_relat_2(X24)
        | ~ v2_wellord1(X24)
        | ~ v1_relat_1(X24) )
      & ( v4_relat_2(X24)
        | ~ v2_wellord1(X24)
        | ~ v1_relat_1(X24) )
      & ( v6_relat_2(X24)
        | ~ v2_wellord1(X24)
        | ~ v1_relat_1(X24) )
      & ( v1_wellord1(X24)
        | ~ v2_wellord1(X24)
        | ~ v1_relat_1(X24) )
      & ( ~ v1_relat_2(X24)
        | ~ v8_relat_2(X24)
        | ~ v4_relat_2(X24)
        | ~ v6_relat_2(X24)
        | ~ v1_wellord1(X24)
        | v2_wellord1(X24)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_18,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22] :
      ( ( X19 != X17
        | ~ r2_hidden(X19,X18)
        | X18 != k1_wellord1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(X19,X17),X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k1_wellord1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( X20 = X17
        | ~ r2_hidden(k4_tarski(X20,X17),X16)
        | r2_hidden(X20,X18)
        | X18 != k1_wellord1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(esk2_3(X16,X21,X22),X22)
        | esk2_3(X16,X21,X22) = X21
        | ~ r2_hidden(k4_tarski(esk2_3(X16,X21,X22),X21),X16)
        | X22 = k1_wellord1(X16,X21)
        | ~ v1_relat_1(X16) )
      & ( esk2_3(X16,X21,X22) != X21
        | r2_hidden(esk2_3(X16,X21,X22),X22)
        | X22 = k1_wellord1(X16,X21)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk2_3(X16,X21,X22),X21),X16)
        | r2_hidden(esk2_3(X16,X21,X22),X22)
        | X22 = k1_wellord1(X16,X21)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( X1 = esk11_0
    | r2_hidden(k4_tarski(esk11_0,X1),esk12_0)
    | r2_hidden(k4_tarski(X1,esk11_0),esk12_0)
    | ~ v6_relat_2(esk12_0)
    | ~ r2_hidden(X1,k3_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_20,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v2_wellord1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( X1 = esk11_0
    | r2_hidden(k4_tarski(X1,esk11_0),esk12_0)
    | r2_hidden(k4_tarski(esk11_0,X1),esk12_0)
    | ~ r2_hidden(X1,k3_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_16])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk10_0,k3_relat_1(esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(k4_tarski(esk11_0,esk10_0),esk12_0)
    | r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)
    | r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)
    | r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_16])])).

fof(c_0_31,plain,(
    ! [X41,X42,X43,X44,X45] :
      ( ( X41 != k3_relat_1(X42)
        | ~ r2_hidden(X44,X41)
        | ~ r2_hidden(k4_tarski(X45,X44),X42)
        | r2_hidden(X45,X41)
        | ~ v2_wellord1(X42)
        | ~ r1_tarski(X41,k3_relat_1(X42))
        | ~ v1_relat_1(X42) )
      & ( ~ r2_hidden(X43,k3_relat_1(X42))
        | X41 != k1_wellord1(X42,X43)
        | ~ r2_hidden(X44,X41)
        | ~ r2_hidden(k4_tarski(X45,X44),X42)
        | r2_hidden(X45,X41)
        | ~ v2_wellord1(X42)
        | ~ r1_tarski(X41,k3_relat_1(X42))
        | ~ v1_relat_1(X42) )
      & ( r2_hidden(esk9_2(X41,X42),k3_relat_1(X42))
        | X41 = k3_relat_1(X42)
        | r2_hidden(esk7_2(X41,X42),X41)
        | ~ v2_wellord1(X42)
        | ~ r1_tarski(X41,k3_relat_1(X42))
        | ~ v1_relat_1(X42) )
      & ( X41 = k1_wellord1(X42,esk9_2(X41,X42))
        | X41 = k3_relat_1(X42)
        | r2_hidden(esk7_2(X41,X42),X41)
        | ~ v2_wellord1(X42)
        | ~ r1_tarski(X41,k3_relat_1(X42))
        | ~ v1_relat_1(X42) )
      & ( r2_hidden(esk9_2(X41,X42),k3_relat_1(X42))
        | X41 = k3_relat_1(X42)
        | r2_hidden(k4_tarski(esk8_2(X41,X42),esk7_2(X41,X42)),X42)
        | ~ v2_wellord1(X42)
        | ~ r1_tarski(X41,k3_relat_1(X42))
        | ~ v1_relat_1(X42) )
      & ( X41 = k1_wellord1(X42,esk9_2(X41,X42))
        | X41 = k3_relat_1(X42)
        | r2_hidden(k4_tarski(esk8_2(X41,X42),esk7_2(X41,X42)),X42)
        | ~ v2_wellord1(X42)
        | ~ r1_tarski(X41,k3_relat_1(X42))
        | ~ v1_relat_1(X42) )
      & ( r2_hidden(esk9_2(X41,X42),k3_relat_1(X42))
        | X41 = k3_relat_1(X42)
        | ~ r2_hidden(esk8_2(X41,X42),X41)
        | ~ v2_wellord1(X42)
        | ~ r1_tarski(X41,k3_relat_1(X42))
        | ~ v1_relat_1(X42) )
      & ( X41 = k1_wellord1(X42,esk9_2(X41,X42))
        | X41 = k3_relat_1(X42)
        | ~ r2_hidden(esk8_2(X41,X42),X41)
        | ~ v2_wellord1(X42)
        | ~ r1_tarski(X41,k3_relat_1(X42))
        | ~ v1_relat_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_wellord1])])])])])).

fof(c_0_32,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X40)
      | r1_tarski(k1_wellord1(X40,X39),k3_relat_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).

fof(c_0_33,plain,(
    ! [X11,X12,X13] :
      ( ( r2_hidden(X11,k3_relat_1(X13))
        | ~ r2_hidden(k4_tarski(X11,X12),X13)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(X12,k3_relat_1(X13))
        | ~ r2_hidden(k4_tarski(X11,X12),X13)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)
    | r2_hidden(X1,k1_wellord1(esk12_0,esk11_0))
    | ~ r2_hidden(X1,k1_wellord1(esk12_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))
    | r2_hidden(esk10_0,k1_wellord1(esk12_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_30]),c_0_16])])).

cnf(c_0_37,plain,
    ( r2_hidden(X5,X3)
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | X3 != k1_wellord1(X2,X1)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(k4_tarski(X5,X4),X2)
    | ~ v2_wellord1(X2)
    | ~ r1_tarski(X3,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(esk10_0,k1_wellord1(esk12_0,esk11_0))
    | r2_hidden(esk11_0,k1_wellord1(esk12_0,esk11_0))
    | r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X2),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,k1_wellord1(X2,X3))
    | ~ r2_hidden(X3,k3_relat_1(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_38])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_wellord1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).

cnf(c_0_47,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(esk11_0,k1_wellord1(esk12_0,esk11_0))
    | r2_hidden(esk10_0,k1_wellord1(esk12_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_42]),c_0_16])])).

cnf(c_0_48,negated_conjecture,
    ( X1 = k1_wellord1(esk12_0,X2)
    | r2_hidden(k4_tarski(esk2_3(esk12_0,X2,X1),X2),esk12_0)
    | r2_hidden(esk2_3(esk12_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_16])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X4,k1_wellord1(X2,X3))
    | ~ r2_hidden(X1,k1_wellord1(X2,X4)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(esk10_0,k1_wellord1(esk12_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_16])])).

fof(c_0_51,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,X15)
      | ~ r1_tarski(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_54,negated_conjecture,
    ( X1 = k1_wellord1(esk12_0,X2)
    | r2_hidden(esk2_3(esk12_0,X2,X1),X1)
    | r2_hidden(X2,k3_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_48]),c_0_16])])).

cnf(c_0_55,negated_conjecture,
    ( esk11_0 = esk10_0
    | r2_hidden(X1,k1_wellord1(esk12_0,esk11_0))
    | ~ r2_hidden(X1,k1_wellord1(esk12_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_21]),c_0_16])])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k1_wellord1(X1,X2) = k1_wellord1(esk12_0,X3)
    | r2_hidden(X3,k3_relat_1(esk12_0))
    | r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( esk11_0 = esk10_0
    | r1_tarski(X1,k1_wellord1(esk12_0,esk11_0))
    | ~ r2_hidden(esk1_2(X1,k1_wellord1(esk12_0,esk11_0)),k1_wellord1(esk12_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_55])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k1_wellord1(esk12_0,X1) = k1_wellord1(esk12_0,X2)
    | r2_hidden(X1,k3_relat_1(esk12_0))
    | r2_hidden(X2,k3_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_16])).

fof(c_0_62,plain,(
    ! [X30,X31,X33,X34] :
      ( ( r2_hidden(X33,k3_relat_1(X30))
        | ~ r2_hidden(X33,esk5_2(X30,X31))
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(X33,X31),X30)
        | ~ r2_hidden(X33,esk5_2(X30,X31))
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(X34,k3_relat_1(X30))
        | r2_hidden(k4_tarski(X34,X31),X30)
        | r2_hidden(X34,esk5_2(X30,X31))
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s1_xboole_0__e7_18__wellord1])])])])])])])).

fof(c_0_63,plain,(
    ! [X35,X36,X38] :
      ( ( r2_hidden(esk6_2(X35,X36),X36)
        | ~ r1_tarski(X36,k3_relat_1(X35))
        | X36 = k1_xboole_0
        | ~ v2_wellord1(X35)
        | ~ v1_relat_1(X35) )
      & ( ~ r2_hidden(X38,X36)
        | r2_hidden(k4_tarski(esk6_2(X35,X36),X38),X35)
        | ~ r1_tarski(X36,k3_relat_1(X35))
        | X36 = k1_xboole_0
        | ~ v2_wellord1(X35)
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord1])])])])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)
    | ~ r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_65,negated_conjecture,
    ( esk11_0 = esk10_0
    | r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( k1_wellord1(esk12_0,X1) = k1_wellord1(esk12_0,k3_relat_1(esk12_0))
    | r2_hidden(X1,k3_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | r1_tarski(k1_wellord1(X2,X1),X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_53])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,esk5_2(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( r2_hidden(k4_tarski(esk6_2(X3,X2),X1),X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,k3_relat_1(X3))
    | ~ v2_wellord1(X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,esk5_2(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( esk11_0 = esk10_0
    | ~ r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk12_0))
    | ~ r2_hidden(X2,k1_wellord1(esk12_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_66]),c_0_16])]),c_0_60])).

cnf(c_0_73,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk12_0))
    | r1_tarski(k1_wellord1(esk12_0,X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_66]),c_0_16])]),c_0_60])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk6_2(X2,X1),esk5_2(X2,X3))
    | ~ r2_hidden(X3,X1)
    | ~ r1_tarski(X1,k3_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( r2_hidden(esk1_2(esk5_2(X1,X2),X3),k3_relat_1(X1))
    | r1_tarski(esk5_2(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_53])).

cnf(c_0_77,negated_conjecture,
    ( esk11_0 = esk10_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_40]),c_0_16])]),c_0_50])).

cnf(c_0_78,negated_conjecture,
    ( k1_wellord1(esk12_0,X1) = k1_xboole_0
    | r2_hidden(X1,k3_relat_1(esk12_0))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_79,plain,
    ( esk5_2(X1,X2) = k1_xboole_0
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,esk5_2(X1,X2))
    | ~ r1_tarski(esk5_2(X1,X2),k3_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_73])).

cnf(c_0_80,plain,
    ( r1_tarski(esk5_2(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk10_0,esk10_0),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_77]),c_0_77]),c_0_57])])).

cnf(c_0_82,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | r2_hidden(X1,esk5_2(X2,X3))
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_83,negated_conjecture,
    ( k1_wellord1(esk12_0,X1) = k1_xboole_0
    | r2_hidden(X1,k3_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_21]),c_0_16])])).

cnf(c_0_84,plain,
    ( esk5_2(X1,X2) = k1_xboole_0
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,esk5_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk10_0,esk5_2(esk12_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_16]),c_0_24])])).

cnf(c_0_86,negated_conjecture,
    ( k1_wellord1(esk12_0,k3_relat_1(esk12_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( esk5_2(esk12_0,esk10_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_21]),c_0_16])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_86]),c_0_16])]),c_0_60])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_87]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.19/0.50  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.030 s
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(t37_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 0.19/0.50  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 0.19/0.50  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 0.19/0.50  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 0.19/0.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.50  fof(t36_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>((v2_wellord1(X2)&r1_tarski(X1,k3_relat_1(X2)))=>(~((X1!=k3_relat_1(X2)&![X3]:~((r2_hidden(X3,k3_relat_1(X2))&X1=k1_wellord1(X2,X3)))))<=>![X3]:(r2_hidden(X3,X1)=>![X4]:(r2_hidden(k4_tarski(X4,X3),X2)=>r2_hidden(X4,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_wellord1)).
% 0.19/0.50  fof(t13_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_wellord1)).
% 0.19/0.50  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 0.19/0.50  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.50  fof(s1_xboole_0__e7_18__wellord1, axiom, ![X1, X2]:(v1_relat_1(X1)=>?[X3]:![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k3_relat_1(X1))&~(r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s1_xboole_0__e7_18__wellord1)).
% 0.19/0.50  fof(t10_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~(((r1_tarski(X2,k3_relat_1(X1))&X2!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X2)&![X4]:(r2_hidden(X4,X2)=>r2_hidden(k4_tarski(X3,X4),X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord1)).
% 0.19/0.50  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)))))), inference(assume_negation,[status(cth)],[t37_wellord1])).
% 0.19/0.50  fof(c_0_12, plain, ![X25, X26, X27]:((~v6_relat_2(X25)|(~r2_hidden(X26,k3_relat_1(X25))|~r2_hidden(X27,k3_relat_1(X25))|X26=X27|r2_hidden(k4_tarski(X26,X27),X25)|r2_hidden(k4_tarski(X27,X26),X25))|~v1_relat_1(X25))&(((((r2_hidden(esk3_1(X25),k3_relat_1(X25))|v6_relat_2(X25)|~v1_relat_1(X25))&(r2_hidden(esk4_1(X25),k3_relat_1(X25))|v6_relat_2(X25)|~v1_relat_1(X25)))&(esk3_1(X25)!=esk4_1(X25)|v6_relat_2(X25)|~v1_relat_1(X25)))&(~r2_hidden(k4_tarski(esk3_1(X25),esk4_1(X25)),X25)|v6_relat_2(X25)|~v1_relat_1(X25)))&(~r2_hidden(k4_tarski(esk4_1(X25),esk3_1(X25)),X25)|v6_relat_2(X25)|~v1_relat_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.19/0.50  fof(c_0_13, negated_conjecture, (v1_relat_1(esk12_0)&(((v2_wellord1(esk12_0)&r2_hidden(esk10_0,k3_relat_1(esk12_0)))&r2_hidden(esk11_0,k3_relat_1(esk12_0)))&((~r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)|~r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)))&(r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)|r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.50  cnf(c_0_14, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.50  cnf(c_0_15, negated_conjecture, (r2_hidden(esk11_0,k3_relat_1(esk12_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.50  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.50  fof(c_0_17, plain, ![X24]:((((((v1_relat_2(X24)|~v2_wellord1(X24)|~v1_relat_1(X24))&(v8_relat_2(X24)|~v2_wellord1(X24)|~v1_relat_1(X24)))&(v4_relat_2(X24)|~v2_wellord1(X24)|~v1_relat_1(X24)))&(v6_relat_2(X24)|~v2_wellord1(X24)|~v1_relat_1(X24)))&(v1_wellord1(X24)|~v2_wellord1(X24)|~v1_relat_1(X24)))&(~v1_relat_2(X24)|~v8_relat_2(X24)|~v4_relat_2(X24)|~v6_relat_2(X24)|~v1_wellord1(X24)|v2_wellord1(X24)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.19/0.50  fof(c_0_18, plain, ![X16, X17, X18, X19, X20, X21, X22]:((((X19!=X17|~r2_hidden(X19,X18)|X18!=k1_wellord1(X16,X17)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(X19,X17),X16)|~r2_hidden(X19,X18)|X18!=k1_wellord1(X16,X17)|~v1_relat_1(X16)))&(X20=X17|~r2_hidden(k4_tarski(X20,X17),X16)|r2_hidden(X20,X18)|X18!=k1_wellord1(X16,X17)|~v1_relat_1(X16)))&((~r2_hidden(esk2_3(X16,X21,X22),X22)|(esk2_3(X16,X21,X22)=X21|~r2_hidden(k4_tarski(esk2_3(X16,X21,X22),X21),X16))|X22=k1_wellord1(X16,X21)|~v1_relat_1(X16))&((esk2_3(X16,X21,X22)!=X21|r2_hidden(esk2_3(X16,X21,X22),X22)|X22=k1_wellord1(X16,X21)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(esk2_3(X16,X21,X22),X21),X16)|r2_hidden(esk2_3(X16,X21,X22),X22)|X22=k1_wellord1(X16,X21)|~v1_relat_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.19/0.50  cnf(c_0_19, negated_conjecture, (X1=esk11_0|r2_hidden(k4_tarski(esk11_0,X1),esk12_0)|r2_hidden(k4_tarski(X1,esk11_0),esk12_0)|~v6_relat_2(esk12_0)|~r2_hidden(X1,k3_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.19/0.50  cnf(c_0_20, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.50  cnf(c_0_21, negated_conjecture, (v2_wellord1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.50  cnf(c_0_22, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.50  cnf(c_0_23, negated_conjecture, (X1=esk11_0|r2_hidden(k4_tarski(X1,esk11_0),esk12_0)|r2_hidden(k4_tarski(esk11_0,X1),esk12_0)|~r2_hidden(X1,k3_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_16])])).
% 0.19/0.50  cnf(c_0_24, negated_conjecture, (r2_hidden(esk10_0,k3_relat_1(esk12_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.50  fof(c_0_25, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.50  cnf(c_0_26, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(er,[status(thm)],[c_0_22])).
% 0.19/0.50  cnf(c_0_27, negated_conjecture, (esk11_0=esk10_0|r2_hidden(k4_tarski(esk11_0,esk10_0),esk12_0)|r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.50  cnf(c_0_28, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.50  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)|r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.50  cnf(c_0_30, negated_conjecture, (esk11_0=esk10_0|r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)|r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_16])])).
% 0.19/0.50  fof(c_0_31, plain, ![X41, X42, X43, X44, X45]:(((X41!=k3_relat_1(X42)|(~r2_hidden(X44,X41)|(~r2_hidden(k4_tarski(X45,X44),X42)|r2_hidden(X45,X41)))|(~v2_wellord1(X42)|~r1_tarski(X41,k3_relat_1(X42)))|~v1_relat_1(X42))&(~r2_hidden(X43,k3_relat_1(X42))|X41!=k1_wellord1(X42,X43)|(~r2_hidden(X44,X41)|(~r2_hidden(k4_tarski(X45,X44),X42)|r2_hidden(X45,X41)))|(~v2_wellord1(X42)|~r1_tarski(X41,k3_relat_1(X42)))|~v1_relat_1(X42)))&(((r2_hidden(esk9_2(X41,X42),k3_relat_1(X42))|X41=k3_relat_1(X42)|r2_hidden(esk7_2(X41,X42),X41)|(~v2_wellord1(X42)|~r1_tarski(X41,k3_relat_1(X42)))|~v1_relat_1(X42))&(X41=k1_wellord1(X42,esk9_2(X41,X42))|X41=k3_relat_1(X42)|r2_hidden(esk7_2(X41,X42),X41)|(~v2_wellord1(X42)|~r1_tarski(X41,k3_relat_1(X42)))|~v1_relat_1(X42)))&(((r2_hidden(esk9_2(X41,X42),k3_relat_1(X42))|X41=k3_relat_1(X42)|r2_hidden(k4_tarski(esk8_2(X41,X42),esk7_2(X41,X42)),X42)|(~v2_wellord1(X42)|~r1_tarski(X41,k3_relat_1(X42)))|~v1_relat_1(X42))&(X41=k1_wellord1(X42,esk9_2(X41,X42))|X41=k3_relat_1(X42)|r2_hidden(k4_tarski(esk8_2(X41,X42),esk7_2(X41,X42)),X42)|(~v2_wellord1(X42)|~r1_tarski(X41,k3_relat_1(X42)))|~v1_relat_1(X42)))&((r2_hidden(esk9_2(X41,X42),k3_relat_1(X42))|X41=k3_relat_1(X42)|~r2_hidden(esk8_2(X41,X42),X41)|(~v2_wellord1(X42)|~r1_tarski(X41,k3_relat_1(X42)))|~v1_relat_1(X42))&(X41=k1_wellord1(X42,esk9_2(X41,X42))|X41=k3_relat_1(X42)|~r2_hidden(esk8_2(X41,X42),X41)|(~v2_wellord1(X42)|~r1_tarski(X41,k3_relat_1(X42)))|~v1_relat_1(X42)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_wellord1])])])])])).
% 0.19/0.50  fof(c_0_32, plain, ![X39, X40]:(~v1_relat_1(X40)|r1_tarski(k1_wellord1(X40,X39),k3_relat_1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).
% 0.19/0.50  fof(c_0_33, plain, ![X11, X12, X13]:((r2_hidden(X11,k3_relat_1(X13))|~r2_hidden(k4_tarski(X11,X12),X13)|~v1_relat_1(X13))&(r2_hidden(X12,k3_relat_1(X13))|~r2_hidden(k4_tarski(X11,X12),X13)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.19/0.50  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.50  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)|r2_hidden(X1,k1_wellord1(esk12_0,esk11_0))|~r2_hidden(X1,k1_wellord1(esk12_0,esk10_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.50  cnf(c_0_36, negated_conjecture, (esk11_0=esk10_0|r2_hidden(esk11_0,k1_wellord1(esk12_0,esk10_0))|r2_hidden(esk10_0,k1_wellord1(esk12_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_30]), c_0_16])])).
% 0.19/0.50  cnf(c_0_37, plain, (r2_hidden(X5,X3)|~r2_hidden(X1,k3_relat_1(X2))|X3!=k1_wellord1(X2,X1)|~r2_hidden(X4,X3)|~r2_hidden(k4_tarski(X5,X4),X2)|~v2_wellord1(X2)|~r1_tarski(X3,k3_relat_1(X2))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.50  cnf(c_0_38, plain, (r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.50  cnf(c_0_39, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.50  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_41, plain, (X1!=X2|~r2_hidden(X1,X3)|X3!=k1_wellord1(X4,X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.50  cnf(c_0_42, negated_conjecture, (esk11_0=esk10_0|r2_hidden(esk10_0,k1_wellord1(esk12_0,esk11_0))|r2_hidden(esk11_0,k1_wellord1(esk12_0,esk11_0))|r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.50  cnf(c_0_43, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X2),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k1_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.50  cnf(c_0_44, plain, (r2_hidden(X1,k1_wellord1(X2,X3))|~v2_wellord1(X2)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,k1_wellord1(X2,X3))|~r2_hidden(X3,k3_relat_1(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_37]), c_0_38])).
% 0.19/0.50  cnf(c_0_45, plain, (r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X3,k1_wellord1(X2,X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.50  cnf(c_0_46, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).
% 0.19/0.50  cnf(c_0_47, negated_conjecture, (esk11_0=esk10_0|r2_hidden(esk11_0,k1_wellord1(esk12_0,esk11_0))|r2_hidden(esk10_0,k1_wellord1(esk12_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_42]), c_0_16])])).
% 0.19/0.50  cnf(c_0_48, negated_conjecture, (X1=k1_wellord1(esk12_0,X2)|r2_hidden(k4_tarski(esk2_3(esk12_0,X2,X1),X2),esk12_0)|r2_hidden(esk2_3(esk12_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_43, c_0_16])).
% 0.19/0.50  cnf(c_0_49, plain, (r2_hidden(X1,k1_wellord1(X2,X3))|~v2_wellord1(X2)|~v1_relat_1(X2)|~r2_hidden(X4,k1_wellord1(X2,X3))|~r2_hidden(X1,k1_wellord1(X2,X4))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_40]), c_0_45])).
% 0.19/0.50  cnf(c_0_50, negated_conjecture, (esk11_0=esk10_0|r2_hidden(esk10_0,k1_wellord1(esk12_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_16])])).
% 0.19/0.50  fof(c_0_51, plain, ![X14, X15]:(~r2_hidden(X14,X15)|~r1_tarski(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.50  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.50  cnf(c_0_53, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.50  cnf(c_0_54, negated_conjecture, (X1=k1_wellord1(esk12_0,X2)|r2_hidden(esk2_3(esk12_0,X2,X1),X1)|r2_hidden(X2,k3_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_48]), c_0_16])])).
% 0.19/0.50  cnf(c_0_55, negated_conjecture, (esk11_0=esk10_0|r2_hidden(X1,k1_wellord1(esk12_0,esk11_0))|~r2_hidden(X1,k1_wellord1(esk12_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_21]), c_0_16])])).
% 0.19/0.50  cnf(c_0_56, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.50  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.50  cnf(c_0_58, negated_conjecture, (k1_wellord1(X1,X2)=k1_wellord1(esk12_0,X3)|r2_hidden(X3,k3_relat_1(esk12_0))|r2_hidden(X2,k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_54])).
% 0.19/0.50  cnf(c_0_59, negated_conjecture, (esk11_0=esk10_0|r1_tarski(X1,k1_wellord1(esk12_0,esk11_0))|~r2_hidden(esk1_2(X1,k1_wellord1(esk12_0,esk11_0)),k1_wellord1(esk12_0,esk10_0))), inference(spm,[status(thm)],[c_0_52, c_0_55])).
% 0.19/0.50  cnf(c_0_60, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.50  cnf(c_0_61, negated_conjecture, (k1_wellord1(esk12_0,X1)=k1_wellord1(esk12_0,X2)|r2_hidden(X1,k3_relat_1(esk12_0))|r2_hidden(X2,k3_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_58, c_0_16])).
% 0.19/0.50  fof(c_0_62, plain, ![X30, X31, X33, X34]:(((r2_hidden(X33,k3_relat_1(X30))|~r2_hidden(X33,esk5_2(X30,X31))|~v1_relat_1(X30))&(~r2_hidden(k4_tarski(X33,X31),X30)|~r2_hidden(X33,esk5_2(X30,X31))|~v1_relat_1(X30)))&(~r2_hidden(X34,k3_relat_1(X30))|r2_hidden(k4_tarski(X34,X31),X30)|r2_hidden(X34,esk5_2(X30,X31))|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s1_xboole_0__e7_18__wellord1])])])])])])])).
% 0.19/0.50  fof(c_0_63, plain, ![X35, X36, X38]:((r2_hidden(esk6_2(X35,X36),X36)|(~r1_tarski(X36,k3_relat_1(X35))|X36=k1_xboole_0)|~v2_wellord1(X35)|~v1_relat_1(X35))&(~r2_hidden(X38,X36)|r2_hidden(k4_tarski(esk6_2(X35,X36),X38),X35)|(~r1_tarski(X36,k3_relat_1(X35))|X36=k1_xboole_0)|~v2_wellord1(X35)|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord1])])])])])).
% 0.19/0.50  cnf(c_0_64, negated_conjecture, (~r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)|~r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.50  cnf(c_0_65, negated_conjecture, (esk11_0=esk10_0|r1_tarski(k1_wellord1(esk12_0,esk10_0),k1_wellord1(esk12_0,esk11_0))), inference(spm,[status(thm)],[c_0_59, c_0_53])).
% 0.19/0.50  cnf(c_0_66, negated_conjecture, (k1_wellord1(esk12_0,X1)=k1_wellord1(esk12_0,k3_relat_1(esk12_0))|r2_hidden(X1,k3_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.50  cnf(c_0_67, plain, (r2_hidden(X1,k3_relat_1(X2))|r1_tarski(k1_wellord1(X2,X1),X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_45, c_0_53])).
% 0.19/0.50  cnf(c_0_68, plain, (~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,esk5_2(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.50  cnf(c_0_69, plain, (r2_hidden(k4_tarski(esk6_2(X3,X2),X1),X3)|X2=k1_xboole_0|~r2_hidden(X1,X2)|~r1_tarski(X2,k3_relat_1(X3))|~v2_wellord1(X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.50  cnf(c_0_70, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(X1,esk5_2(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.50  cnf(c_0_71, negated_conjecture, (esk11_0=esk10_0|~r2_hidden(k4_tarski(esk10_0,esk11_0),esk12_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.50  cnf(c_0_72, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk12_0))|~r2_hidden(X2,k1_wellord1(esk12_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_66]), c_0_16])]), c_0_60])).
% 0.19/0.50  cnf(c_0_73, plain, (r2_hidden(esk6_2(X1,X2),X2)|X2=k1_xboole_0|~r1_tarski(X2,k3_relat_1(X1))|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.50  cnf(c_0_74, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk12_0))|r1_tarski(k1_wellord1(esk12_0,X1),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_66]), c_0_16])]), c_0_60])).
% 0.19/0.50  cnf(c_0_75, plain, (X1=k1_xboole_0|~v2_wellord1(X2)|~v1_relat_1(X2)|~r2_hidden(esk6_2(X2,X1),esk5_2(X2,X3))|~r2_hidden(X3,X1)|~r1_tarski(X1,k3_relat_1(X2))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.50  cnf(c_0_76, plain, (r2_hidden(esk1_2(esk5_2(X1,X2),X3),k3_relat_1(X1))|r1_tarski(esk5_2(X1,X2),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_70, c_0_53])).
% 0.19/0.50  cnf(c_0_77, negated_conjecture, (esk11_0=esk10_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_40]), c_0_16])]), c_0_50])).
% 0.19/0.50  cnf(c_0_78, negated_conjecture, (k1_wellord1(esk12_0,X1)=k1_xboole_0|r2_hidden(X1,k3_relat_1(esk12_0))|~v2_wellord1(X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 0.19/0.50  cnf(c_0_79, plain, (esk5_2(X1,X2)=k1_xboole_0|~v2_wellord1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,esk5_2(X1,X2))|~r1_tarski(esk5_2(X1,X2),k3_relat_1(X1))), inference(spm,[status(thm)],[c_0_75, c_0_73])).
% 0.19/0.50  cnf(c_0_80, plain, (r1_tarski(esk5_2(X1,X2),k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_76])).
% 0.19/0.50  cnf(c_0_81, negated_conjecture, (~r2_hidden(k4_tarski(esk10_0,esk10_0),esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_77]), c_0_77]), c_0_57])])).
% 0.19/0.50  cnf(c_0_82, plain, (r2_hidden(k4_tarski(X1,X3),X2)|r2_hidden(X1,esk5_2(X2,X3))|~r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.50  cnf(c_0_83, negated_conjecture, (k1_wellord1(esk12_0,X1)=k1_xboole_0|r2_hidden(X1,k3_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_21]), c_0_16])])).
% 0.19/0.50  cnf(c_0_84, plain, (esk5_2(X1,X2)=k1_xboole_0|~v2_wellord1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,esk5_2(X1,X2))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.50  cnf(c_0_85, negated_conjecture, (r2_hidden(esk10_0,esk5_2(esk12_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_16]), c_0_24])])).
% 0.19/0.50  cnf(c_0_86, negated_conjecture, (k1_wellord1(esk12_0,k3_relat_1(esk12_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_83])).
% 0.19/0.50  cnf(c_0_87, negated_conjecture, (esk5_2(esk12_0,esk10_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_21]), c_0_16])])).
% 0.19/0.50  cnf(c_0_88, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_86]), c_0_16])]), c_0_60])).
% 0.19/0.50  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_87]), c_0_88]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 90
% 0.19/0.50  # Proof object clause steps            : 67
% 0.19/0.50  # Proof object formula steps           : 23
% 0.19/0.50  # Proof object conjectures             : 38
% 0.19/0.50  # Proof object clause conjectures      : 35
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 24
% 0.19/0.50  # Proof object initial formulas used   : 11
% 0.19/0.50  # Proof object generating inferences   : 37
% 0.19/0.50  # Proof object simplifying inferences  : 52
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 11
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 44
% 0.19/0.50  # Removed in clause preprocessing      : 0
% 0.19/0.50  # Initial clauses in saturation        : 44
% 0.19/0.50  # Processed clauses                    : 920
% 0.19/0.50  # ...of these trivial                  : 10
% 0.19/0.50  # ...subsumed                          : 498
% 0.19/0.50  # ...remaining for further processing  : 412
% 0.19/0.50  # Other redundant clauses eliminated   : 6
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 52
% 0.19/0.50  # Backward-rewritten                   : 125
% 0.19/0.50  # Generated clauses                    : 3957
% 0.19/0.50  # ...of the previous two non-trivial   : 3708
% 0.19/0.50  # Contextual simplify-reflections      : 13
% 0.19/0.50  # Paramodulations                      : 3948
% 0.19/0.50  # Factorizations                       : 4
% 0.19/0.50  # Equation resolutions                 : 6
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 230
% 0.19/0.50  #    Positive orientable unit clauses  : 9
% 0.19/0.50  #    Positive unorientable unit clauses: 0
% 0.19/0.50  #    Negative unit clauses             : 6
% 0.19/0.50  #    Non-unit-clauses                  : 215
% 0.19/0.50  # Current number of unprocessed clauses: 2658
% 0.19/0.50  # ...number of literals in the above   : 18406
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 177
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 29927
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 4273
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 391
% 0.19/0.50  # Unit Clause-clause subsumption calls : 564
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 12
% 0.19/0.50  # BW rewrite match successes           : 5
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 99185
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.154 s
% 0.19/0.50  # System time              : 0.008 s
% 0.19/0.50  # Total time               : 0.161 s
% 0.19/0.50  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
