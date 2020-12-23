%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:55 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 863 expanded)
%              Number of clauses        :   56 ( 356 expanded)
%              Number of leaves         :   12 ( 205 expanded)
%              Depth                    :   18
%              Number of atoms          :  335 (4530 expanded)
%              Number of equality atoms :   31 ( 473 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t13_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(t35_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k1_wellord1(X3,X2)) )
       => k1_wellord1(k2_wellord1(X3,k1_wellord1(X3,X2)),X1) = k1_wellord1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(t19_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) )
         => ( r2_hidden(k4_tarski(X1,X2),X3)
          <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_wellord1])).

fof(c_0_13,plain,(
    ! [X27,X28] :
      ( ( ~ v1_relat_2(X27)
        | ~ r2_hidden(X28,k3_relat_1(X27))
        | r2_hidden(k4_tarski(X28,X28),X27)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(esk3_1(X27),k3_relat_1(X27))
        | v1_relat_2(X27)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X27),esk3_1(X27)),X27)
        | v1_relat_2(X27)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v2_wellord1(esk8_0)
    & r2_hidden(esk6_0,k3_relat_1(esk8_0))
    & r2_hidden(esk7_0,k3_relat_1(esk8_0))
    & ( ~ r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
      | ~ r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)) )
    & ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
      | r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk6_0,k3_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
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

fof(c_0_20,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v6_relat_2(X30)
        | ~ r2_hidden(X31,k3_relat_1(X30))
        | ~ r2_hidden(X32,k3_relat_1(X30))
        | X31 = X32
        | r2_hidden(k4_tarski(X31,X32),X30)
        | r2_hidden(k4_tarski(X32,X31),X30)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(esk4_1(X30),k3_relat_1(X30))
        | v6_relat_2(X30)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(esk5_1(X30),k3_relat_1(X30))
        | v6_relat_2(X30)
        | ~ v1_relat_1(X30) )
      & ( esk4_1(X30) != esk5_1(X30)
        | v6_relat_2(X30)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(esk4_1(X30),esk5_1(X30)),X30)
        | v6_relat_2(X30)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(esk5_1(X30),esk4_1(X30)),X30)
        | v6_relat_2(X30)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
    | ~ r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk6_0),esk8_0)
    | ~ v1_relat_2(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_25,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v2_wellord1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_27,plain,(
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

cnf(c_0_28,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,X1),esk8_0)
    | ~ r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,X1))
    | ~ r1_tarski(esk7_0,X1)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk6_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_18])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),X2)
    | r2_hidden(k4_tarski(esk7_0,X1),X2)
    | ~ v6_relat_2(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk6_0,X1),esk8_0)
    | ~ r2_hidden(esk7_0,k3_relat_1(X2))
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(esk7_0,esk6_0)
    | ~ r1_tarski(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk6_0),X1)
    | r2_hidden(k4_tarski(esk6_0,esk7_0),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk7_0,k3_relat_1(X1))
    | ~ r2_hidden(esk6_0,k3_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_31])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk7_0,k3_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,k1_wellord1(X2,esk6_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,esk6_0),X2)
    | ~ r1_tarski(esk7_0,X1)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r2_hidden(k4_tarski(esk7_0,esk6_0),esk8_0)
    | ~ v6_relat_2(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_18]),c_0_17])])).

cnf(c_0_40,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_0,k1_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk6_0,X2),X1)
    | ~ r1_tarski(esk7_0,X2)
    | ~ r1_tarski(X2,esk7_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r1_tarski(esk7_0,X1)
    | ~ r1_tarski(X1,esk7_0)
    | ~ r1_tarski(X3,esk6_0)
    | ~ r1_tarski(esk6_0,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk6_0),esk8_0)
    | r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_26]),c_0_18])])).

fof(c_0_44,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r1_tarski(esk7_0,X3)
    | ~ r1_tarski(X3,esk7_0)
    | ~ r1_tarski(X1,esk6_0)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r2_hidden(esk7_0,k1_wellord1(esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_18]),c_0_30]),c_0_30])])).

fof(c_0_47,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_48,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk7_0,k1_wellord1(esk8_0,esk6_0))
    | r2_hidden(esk6_0,k1_wellord1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_18]),c_0_30]),c_0_30])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk6_0,k1_wellord1(esk8_0,esk7_0))
    | r2_hidden(esk7_0,X1)
    | ~ r1_tarski(k1_wellord1(esk8_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r1_tarski(X1,k1_wellord1(esk8_0,esk7_0))
    | ~ r1_tarski(X1,k1_wellord1(esk8_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r2_hidden(esk7_0,k1_wellord1(esk8_0,esk7_0))
    | r2_hidden(esk6_0,k1_wellord1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_30])])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_58,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk7_0,k1_wellord1(esk8_0,esk7_0))
    | r2_hidden(esk6_0,k1_wellord1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_55]),c_0_18]),c_0_30]),c_0_30])])).

fof(c_0_60,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | r1_tarski(k1_wellord1(X36,X35),k3_relat_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).

fof(c_0_61,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ v2_wellord1(X42)
      | ~ r2_hidden(X40,k1_wellord1(X42,X41))
      | k1_wellord1(k2_wellord1(X42,k1_wellord1(X42,X41)),X40) = k1_wellord1(X42,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_wellord1])])).

fof(c_0_62,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | v1_relat_1(k2_wellord1(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_2(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)),k1_wellord1(esk8_0,esk6_0))
    | ~ r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_56])).

cnf(c_0_64,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk6_0,k1_wellord1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_18])])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X3)),X2) = k1_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk1_2(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)),X1)
    | ~ r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
    | ~ r1_tarski(k1_wellord1(esk8_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_18])])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X3))))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_73,plain,(
    ! [X37,X38,X39] :
      ( ( r2_hidden(X37,k3_relat_1(X39))
        | ~ r2_hidden(X37,k3_relat_1(k2_wellord1(X39,X38)))
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(X37,X38)
        | ~ r2_hidden(X37,k3_relat_1(k2_wellord1(X39,X38)))
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_2(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)),X1)
    | ~ r1_tarski(k1_wellord1(esk8_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk8_0,esk6_0),k3_relat_1(k2_wellord1(esk8_0,k1_wellord1(esk8_0,esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_65]),c_0_26]),c_0_18])])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(esk1_2(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)),k1_wellord1(esk8_0,esk7_0))
    | ~ r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_72])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk1_2(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)),k3_relat_1(k2_wellord1(esk8_0,k1_wellord1(esk8_0,esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(esk1_2(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)),k1_wellord1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_70])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_18])]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 2.25/2.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 2.25/2.50  # and selection function PSelectUnlessUniqMaxPos.
% 2.25/2.50  #
% 2.25/2.50  # Preprocessing time       : 0.029 s
% 2.25/2.50  # Presaturation interreduction done
% 2.25/2.50  
% 2.25/2.50  # Proof found!
% 2.25/2.50  # SZS status Theorem
% 2.25/2.50  # SZS output start CNFRefutation
% 2.25/2.50  fof(t37_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 2.25/2.50  fof(l1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>![X2]:(r2_hidden(X2,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 2.25/2.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.25/2.50  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 2.25/2.50  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 2.25/2.50  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 2.25/2.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.25/2.50  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.25/2.50  fof(t13_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_wellord1)).
% 2.25/2.50  fof(t35_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((v2_wellord1(X3)&r2_hidden(X1,k1_wellord1(X3,X2)))=>k1_wellord1(k2_wellord1(X3,k1_wellord1(X3,X2)),X1)=k1_wellord1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_wellord1)).
% 2.25/2.50  fof(dt_k2_wellord1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k2_wellord1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 2.25/2.50  fof(t19_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_wellord1)).
% 2.25/2.50  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)))))), inference(assume_negation,[status(cth)],[t37_wellord1])).
% 2.25/2.50  fof(c_0_13, plain, ![X27, X28]:((~v1_relat_2(X27)|(~r2_hidden(X28,k3_relat_1(X27))|r2_hidden(k4_tarski(X28,X28),X27))|~v1_relat_1(X27))&((r2_hidden(esk3_1(X27),k3_relat_1(X27))|v1_relat_2(X27)|~v1_relat_1(X27))&(~r2_hidden(k4_tarski(esk3_1(X27),esk3_1(X27)),X27)|v1_relat_2(X27)|~v1_relat_1(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).
% 2.25/2.50  fof(c_0_14, negated_conjecture, (v1_relat_1(esk8_0)&(((v2_wellord1(esk8_0)&r2_hidden(esk6_0,k3_relat_1(esk8_0)))&r2_hidden(esk7_0,k3_relat_1(esk8_0)))&((~r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|~r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)))&(r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 2.25/2.50  fof(c_0_15, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.25/2.50  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X2,X2),X1)|~v1_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.25/2.50  cnf(c_0_17, negated_conjecture, (r2_hidden(esk6_0,k3_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.25/2.50  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.25/2.50  fof(c_0_19, plain, ![X24]:((((((v1_relat_2(X24)|~v2_wellord1(X24)|~v1_relat_1(X24))&(v8_relat_2(X24)|~v2_wellord1(X24)|~v1_relat_1(X24)))&(v4_relat_2(X24)|~v2_wellord1(X24)|~v1_relat_1(X24)))&(v6_relat_2(X24)|~v2_wellord1(X24)|~v1_relat_1(X24)))&(v1_wellord1(X24)|~v2_wellord1(X24)|~v1_relat_1(X24)))&(~v1_relat_2(X24)|~v8_relat_2(X24)|~v4_relat_2(X24)|~v6_relat_2(X24)|~v1_wellord1(X24)|v2_wellord1(X24)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 2.25/2.50  fof(c_0_20, plain, ![X30, X31, X32]:((~v6_relat_2(X30)|(~r2_hidden(X31,k3_relat_1(X30))|~r2_hidden(X32,k3_relat_1(X30))|X31=X32|r2_hidden(k4_tarski(X31,X32),X30)|r2_hidden(k4_tarski(X32,X31),X30))|~v1_relat_1(X30))&(((((r2_hidden(esk4_1(X30),k3_relat_1(X30))|v6_relat_2(X30)|~v1_relat_1(X30))&(r2_hidden(esk5_1(X30),k3_relat_1(X30))|v6_relat_2(X30)|~v1_relat_1(X30)))&(esk4_1(X30)!=esk5_1(X30)|v6_relat_2(X30)|~v1_relat_1(X30)))&(~r2_hidden(k4_tarski(esk4_1(X30),esk5_1(X30)),X30)|v6_relat_2(X30)|~v1_relat_1(X30)))&(~r2_hidden(k4_tarski(esk5_1(X30),esk4_1(X30)),X30)|v6_relat_2(X30)|~v1_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 2.25/2.50  cnf(c_0_21, negated_conjecture, (~r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|~r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.25/2.50  cnf(c_0_22, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.25/2.50  cnf(c_0_23, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.25/2.50  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk6_0),esk8_0)|~v1_relat_2(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 2.25/2.50  cnf(c_0_25, plain, (v1_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.25/2.50  cnf(c_0_26, negated_conjecture, (v2_wellord1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.25/2.50  fof(c_0_27, plain, ![X16, X17, X18, X19, X20, X21, X22]:((((X19!=X17|~r2_hidden(X19,X18)|X18!=k1_wellord1(X16,X17)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(X19,X17),X16)|~r2_hidden(X19,X18)|X18!=k1_wellord1(X16,X17)|~v1_relat_1(X16)))&(X20=X17|~r2_hidden(k4_tarski(X20,X17),X16)|r2_hidden(X20,X18)|X18!=k1_wellord1(X16,X17)|~v1_relat_1(X16)))&((~r2_hidden(esk2_3(X16,X21,X22),X22)|(esk2_3(X16,X21,X22)=X21|~r2_hidden(k4_tarski(esk2_3(X16,X21,X22),X21),X16))|X22=k1_wellord1(X16,X21)|~v1_relat_1(X16))&((esk2_3(X16,X21,X22)!=X21|r2_hidden(esk2_3(X16,X21,X22),X22)|X22=k1_wellord1(X16,X21)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(esk2_3(X16,X21,X22),X21),X16)|r2_hidden(esk2_3(X16,X21,X22),X22)|X22=k1_wellord1(X16,X21)|~v1_relat_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 2.25/2.50  cnf(c_0_28, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.25/2.50  cnf(c_0_29, negated_conjecture, (~r2_hidden(k4_tarski(esk6_0,X1),esk8_0)|~r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,X1))|~r1_tarski(esk7_0,X1)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 2.25/2.50  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_23])).
% 2.25/2.50  cnf(c_0_31, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk6_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_18])])).
% 2.25/2.50  cnf(c_0_32, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.25/2.50  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),X2)|r2_hidden(k4_tarski(esk7_0,X1),X2)|~v6_relat_2(X2)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(esk6_0,X1),esk8_0)|~r2_hidden(esk7_0,k3_relat_1(X2))|~r2_hidden(X1,k3_relat_1(X2))|~r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_21, c_0_28])).
% 2.25/2.50  cnf(c_0_34, negated_conjecture, (~r1_tarski(esk7_0,esk6_0)|~r1_tarski(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 2.25/2.50  cnf(c_0_35, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(er,[status(thm)],[c_0_32])).
% 2.25/2.50  cnf(c_0_36, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk6_0),X1)|r2_hidden(k4_tarski(esk6_0,esk7_0),X1)|~v6_relat_2(X1)|~v1_relat_1(X1)|~r2_hidden(esk7_0,k3_relat_1(X1))|~r2_hidden(esk6_0,k3_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_30]), c_0_31])])).
% 2.25/2.50  cnf(c_0_37, negated_conjecture, (r2_hidden(esk7_0,k3_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.25/2.50  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,k1_wellord1(X2,esk6_0))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,esk6_0),X2)|~r1_tarski(esk7_0,X1)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 2.25/2.50  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|r2_hidden(k4_tarski(esk7_0,esk6_0),esk8_0)|~v6_relat_2(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_18]), c_0_17])])).
% 2.25/2.50  cnf(c_0_40, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.25/2.50  cnf(c_0_41, negated_conjecture, (r2_hidden(esk6_0,k1_wellord1(X1,X2))|~v1_relat_1(X1)|~r2_hidden(k4_tarski(esk6_0,X2),X1)|~r1_tarski(esk7_0,X2)|~r1_tarski(X2,esk7_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 2.25/2.50  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,k1_wellord1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X3),X2)|~r1_tarski(esk7_0,X1)|~r1_tarski(X1,esk7_0)|~r1_tarski(X3,esk6_0)|~r1_tarski(esk6_0,X3)), inference(spm,[status(thm)],[c_0_38, c_0_22])).
% 2.25/2.50  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk6_0),esk8_0)|r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_26]), c_0_18])])).
% 2.25/2.50  fof(c_0_44, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.25/2.50  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,k1_wellord1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X3),X2)|~r1_tarski(esk7_0,X3)|~r1_tarski(X3,esk7_0)|~r1_tarski(X1,esk6_0)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_22])).
% 2.25/2.50  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|r2_hidden(esk7_0,k1_wellord1(esk8_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_18]), c_0_30]), c_0_30])])).
% 2.25/2.50  fof(c_0_47, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 2.25/2.50  cnf(c_0_48, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.25/2.50  cnf(c_0_49, negated_conjecture, (r2_hidden(esk7_0,k1_wellord1(esk8_0,esk6_0))|r2_hidden(esk6_0,k1_wellord1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_18]), c_0_30]), c_0_30])])).
% 2.25/2.50  cnf(c_0_50, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.25/2.50  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.25/2.50  cnf(c_0_52, negated_conjecture, (r2_hidden(esk6_0,k1_wellord1(esk8_0,esk7_0))|r2_hidden(esk7_0,X1)|~r1_tarski(k1_wellord1(esk8_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 2.25/2.50  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|r1_tarski(X1,k1_wellord1(esk8_0,esk7_0))|~r1_tarski(X1,k1_wellord1(esk8_0,esk6_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 2.25/2.50  cnf(c_0_54, plain, (X1!=X2|~r2_hidden(X1,X3)|X3!=k1_wellord1(X4,X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.25/2.50  cnf(c_0_55, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|r2_hidden(esk7_0,k1_wellord1(esk8_0,esk7_0))|r2_hidden(esk6_0,k1_wellord1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_30])])).
% 2.25/2.50  cnf(c_0_56, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.25/2.50  cnf(c_0_57, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.25/2.50  cnf(c_0_58, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).
% 2.25/2.50  cnf(c_0_59, negated_conjecture, (r2_hidden(esk7_0,k1_wellord1(esk8_0,esk7_0))|r2_hidden(esk6_0,k1_wellord1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_55]), c_0_18]), c_0_30]), c_0_30])])).
% 2.25/2.50  fof(c_0_60, plain, ![X35, X36]:(~v1_relat_1(X36)|r1_tarski(k1_wellord1(X36,X35),k3_relat_1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).
% 2.25/2.50  fof(c_0_61, plain, ![X40, X41, X42]:(~v1_relat_1(X42)|(~v2_wellord1(X42)|~r2_hidden(X40,k1_wellord1(X42,X41))|k1_wellord1(k2_wellord1(X42,k1_wellord1(X42,X41)),X40)=k1_wellord1(X42,X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_wellord1])])).
% 2.25/2.50  fof(c_0_62, plain, ![X25, X26]:(~v1_relat_1(X25)|v1_relat_1(k2_wellord1(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).
% 2.25/2.50  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_2(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)),k1_wellord1(esk8_0,esk6_0))|~r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_21, c_0_56])).
% 2.25/2.50  cnf(c_0_64, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_57])).
% 2.25/2.50  cnf(c_0_65, negated_conjecture, (r2_hidden(esk6_0,k1_wellord1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_18])])).
% 2.25/2.50  cnf(c_0_66, plain, (r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 2.25/2.50  cnf(c_0_67, plain, (k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X3)),X2)=k1_wellord1(X1,X2)|~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k1_wellord1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 2.25/2.50  cnf(c_0_68, plain, (v1_relat_1(k2_wellord1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 2.25/2.50  cnf(c_0_69, negated_conjecture, (r2_hidden(esk1_2(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)),X1)|~r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|~r1_tarski(k1_wellord1(esk8_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_48, c_0_63])).
% 2.25/2.50  cnf(c_0_70, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_18])])).
% 2.25/2.50  cnf(c_0_71, plain, (r1_tarski(k1_wellord1(X1,X2),k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X3))))|~v2_wellord1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 2.25/2.50  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.25/2.50  fof(c_0_73, plain, ![X37, X38, X39]:((r2_hidden(X37,k3_relat_1(X39))|~r2_hidden(X37,k3_relat_1(k2_wellord1(X39,X38)))|~v1_relat_1(X39))&(r2_hidden(X37,X38)|~r2_hidden(X37,k3_relat_1(k2_wellord1(X39,X38)))|~v1_relat_1(X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).
% 2.25/2.50  cnf(c_0_74, negated_conjecture, (r2_hidden(esk1_2(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)),X1)|~r1_tarski(k1_wellord1(esk8_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])])).
% 2.25/2.50  cnf(c_0_75, negated_conjecture, (r1_tarski(k1_wellord1(esk8_0,esk6_0),k3_relat_1(k2_wellord1(esk8_0,k1_wellord1(esk8_0,esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_65]), c_0_26]), c_0_18])])).
% 2.25/2.50  cnf(c_0_76, negated_conjecture, (~r2_hidden(esk1_2(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)),k1_wellord1(esk8_0,esk7_0))|~r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_21, c_0_72])).
% 2.25/2.50  cnf(c_0_77, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 2.25/2.50  cnf(c_0_78, negated_conjecture, (r2_hidden(esk1_2(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)),k3_relat_1(k2_wellord1(esk8_0,k1_wellord1(esk8_0,esk7_0))))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 2.25/2.50  cnf(c_0_79, negated_conjecture, (~r2_hidden(esk1_2(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)),k1_wellord1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_70])])).
% 2.25/2.50  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_18])]), c_0_79]), ['proof']).
% 2.25/2.50  # SZS output end CNFRefutation
% 2.25/2.50  # Proof object total steps             : 81
% 2.25/2.50  # Proof object clause steps            : 56
% 2.25/2.50  # Proof object formula steps           : 25
% 2.25/2.50  # Proof object conjectures             : 37
% 2.25/2.50  # Proof object clause conjectures      : 34
% 2.25/2.50  # Proof object formula conjectures     : 3
% 2.25/2.50  # Proof object initial clauses used    : 23
% 2.25/2.50  # Proof object initial formulas used   : 12
% 2.25/2.50  # Proof object generating inferences   : 27
% 2.25/2.50  # Proof object simplifying inferences  : 49
% 2.25/2.50  # Training examples: 0 positive, 0 negative
% 2.25/2.50  # Parsed axioms                        : 12
% 2.25/2.50  # Removed by relevancy pruning/SinE    : 0
% 2.25/2.50  # Initial clauses                      : 39
% 2.25/2.50  # Removed in clause preprocessing      : 0
% 2.25/2.50  # Initial clauses in saturation        : 39
% 2.25/2.50  # Processed clauses                    : 8246
% 2.25/2.50  # ...of these trivial                  : 42
% 2.25/2.50  # ...subsumed                          : 5645
% 2.25/2.50  # ...remaining for further processing  : 2559
% 2.25/2.50  # Other redundant clauses eliminated   : 35
% 2.25/2.50  # Clauses deleted for lack of memory   : 0
% 2.25/2.50  # Backward-subsumed                    : 337
% 2.25/2.50  # Backward-rewritten                   : 656
% 2.25/2.50  # Generated clauses                    : 139869
% 2.25/2.50  # ...of the previous two non-trivial   : 135201
% 2.25/2.50  # Contextual simplify-reflections      : 27
% 2.25/2.50  # Paramodulations                      : 139471
% 2.25/2.50  # Factorizations                       : 364
% 2.25/2.50  # Equation resolutions                 : 35
% 2.25/2.50  # Propositional unsat checks           : 0
% 2.25/2.50  #    Propositional check models        : 0
% 2.25/2.50  #    Propositional check unsatisfiable : 0
% 2.25/2.50  #    Propositional clauses             : 0
% 2.25/2.50  #    Propositional clauses after purity: 0
% 2.25/2.50  #    Propositional unsat core size     : 0
% 2.25/2.50  #    Propositional preprocessing time  : 0.000
% 2.25/2.50  #    Propositional encoding time       : 0.000
% 2.25/2.50  #    Propositional solver time         : 0.000
% 2.25/2.50  #    Success case prop preproc time    : 0.000
% 2.25/2.50  #    Success case prop encoding time   : 0.000
% 2.25/2.50  #    Success case prop solver time     : 0.000
% 2.25/2.50  # Current number of processed clauses  : 1523
% 2.25/2.50  #    Positive orientable unit clauses  : 25
% 2.25/2.50  #    Positive unorientable unit clauses: 0
% 2.25/2.50  #    Negative unit clauses             : 6
% 2.25/2.50  #    Non-unit-clauses                  : 1492
% 2.25/2.50  # Current number of unprocessed clauses: 125824
% 2.25/2.50  # ...number of literals in the above   : 1073287
% 2.25/2.50  # Current number of archived formulas  : 0
% 2.25/2.50  # Current number of archived clauses   : 1031
% 2.25/2.50  # Clause-clause subsumption calls (NU) : 719440
% 2.25/2.50  # Rec. Clause-clause subsumption calls : 72499
% 2.25/2.50  # Non-unit clause-clause subsumptions  : 5734
% 2.25/2.50  # Unit Clause-clause subsumption calls : 1988
% 2.25/2.50  # Rewrite failures with RHS unbound    : 0
% 2.25/2.50  # BW rewrite match attempts            : 70
% 2.25/2.50  # BW rewrite match successes           : 10
% 2.25/2.50  # Condensation attempts                : 0
% 2.25/2.50  # Condensation successes               : 0
% 2.25/2.50  # Termbank termtop insertions          : 3858777
% 2.34/2.50  
% 2.34/2.50  # -------------------------------------------------
% 2.34/2.50  # User time                : 2.079 s
% 2.34/2.50  # System time              : 0.083 s
% 2.34/2.50  # Total time               : 2.162 s
% 2.34/2.50  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
