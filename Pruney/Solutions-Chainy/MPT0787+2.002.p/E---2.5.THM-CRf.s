%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:55 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 457 expanded)
%              Number of clauses        :   47 ( 187 expanded)
%              Number of leaves         :   11 ( 111 expanded)
%              Depth                    :   14
%              Number of atoms          :  303 (2259 expanded)
%              Number of equality atoms :   30 ( 225 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t20_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))
        & r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(t13_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(t35_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k1_wellord1(X3,X2)) )
       => k1_wellord1(k2_wellord1(X3,k1_wellord1(X3,X2)),X1) = k1_wellord1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_wellord1)).

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

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v2_wellord1(esk8_0)
    & r2_hidden(esk6_0,k3_relat_1(esk8_0))
    & r2_hidden(esk7_0,k3_relat_1(esk8_0))
    & ( ~ r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
      | ~ r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)) )
    & ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
      | r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk6_0,k3_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
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

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
    | ~ r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk6_0),esk8_0)
    | ~ v1_relat_2(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_23,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v2_wellord1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
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

fof(c_0_26,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_27,plain,(
    ! [X37,X38] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X38,X37)),k3_relat_1(X38))
        | ~ v1_relat_1(X38) )
      & ( r1_tarski(k3_relat_1(k2_wellord1(X38,X37)),X37)
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_wellord1])])])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,X1),esk8_0)
    | ~ r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,X1))
    | ~ r1_tarski(esk7_0,X1)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk6_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_17])])).

fof(c_0_31,plain,(
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

cnf(c_0_32,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | r1_tarski(k1_wellord1(X36,X35),k3_relat_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).

fof(c_0_36,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | v1_relat_1(k2_wellord1(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(esk7_0,esk6_0)
    | ~ r1_tarski(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_38,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk7_0,k3_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,X1),X2)
    | r2_hidden(k4_tarski(X1,esk6_0),X2)
    | ~ v6_relat_2(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk6_0,k3_relat_1(X2))
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ r1_tarski(esk7_0,X1)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk8_0))
    | ~ r1_tarski(esk7_0,X1)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_20])).

cnf(c_0_47,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(k1_wellord1(X1,X2),X3)
    | ~ r1_tarski(X3,k1_wellord1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_20])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_wellord1(k2_wellord1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

fof(c_0_49,plain,(
    ! [X39,X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ v2_wellord1(X41)
      | ~ r2_hidden(X39,k1_wellord1(X41,X40))
      | k1_wellord1(k2_wellord1(X41,k1_wellord1(X41,X40)),X39) = k1_wellord1(X41,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_wellord1])])).

cnf(c_0_50,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk6_0),esk8_0)
    | r2_hidden(k4_tarski(esk6_0,X1),esk8_0)
    | ~ v6_relat_2(esk8_0)
    | ~ r1_tarski(esk7_0,X1)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_16]),c_0_17])]),c_0_46])).

cnf(c_0_52,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_53,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,k1_wellord1(k2_wellord1(X1,X3),X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_43])).

cnf(c_0_54,plain,
    ( k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X3)),X2) = k1_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,k1_wellord1(X2,esk6_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,esk6_0),X2)
    | ~ r1_tarski(esk7_0,X1)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,X1),esk8_0)
    | r2_hidden(k4_tarski(X1,esk6_0),esk8_0)
    | ~ r1_tarski(esk7_0,X1)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_24]),c_0_17])])).

cnf(c_0_57,plain,
    ( ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X3))
    | ~ r1_tarski(k1_wellord1(X1,X3),k1_wellord1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk6_0,k1_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk6_0,X2),X1)
    | ~ r1_tarski(esk7_0,X2)
    | ~ r1_tarski(X2,esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r1_tarski(esk7_0,X1)
    | ~ r1_tarski(X1,esk7_0)
    | ~ r1_tarski(X3,esk6_0)
    | ~ r1_tarski(esk6_0,X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk6_0),esk8_0)
    | r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_29]),c_0_29])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
    | ~ r2_hidden(esk7_0,k1_wellord1(esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_24]),c_0_17])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r1_tarski(esk7_0,X3)
    | ~ r1_tarski(X3,esk7_0)
    | ~ r1_tarski(X1,esk6_0)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_20])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_17]),c_0_29]),c_0_29])]),c_0_62])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X3))))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_54]),c_0_43])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk6_0,k1_wellord1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_17]),c_0_29]),c_0_29])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk8_0,esk6_0),k3_relat_1(k2_wellord1(esk8_0,k1_wellord1(esk8_0,esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_24]),c_0_17])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_64])])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_67]),c_0_17])]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:45:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 3.47/3.65  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 3.47/3.65  # and selection function PSelectUnlessUniqMaxPos.
% 3.47/3.65  #
% 3.47/3.65  # Preprocessing time       : 0.029 s
% 3.47/3.65  # Presaturation interreduction done
% 3.47/3.65  
% 3.47/3.65  # Proof found!
% 3.47/3.65  # SZS status Theorem
% 3.47/3.65  # SZS output start CNFRefutation
% 3.47/3.65  fof(t37_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_wellord1)).
% 3.47/3.65  fof(l1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>![X2]:(r2_hidden(X2,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_wellord1)).
% 3.47/3.65  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.47/3.65  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 3.47/3.65  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 3.47/3.65  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.47/3.65  fof(t20_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))&r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_wellord1)).
% 3.47/3.65  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l4_wellord1)).
% 3.47/3.65  fof(t13_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_wellord1)).
% 3.47/3.65  fof(dt_k2_wellord1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k2_wellord1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 3.47/3.65  fof(t35_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((v2_wellord1(X3)&r2_hidden(X1,k1_wellord1(X3,X2)))=>k1_wellord1(k2_wellord1(X3,k1_wellord1(X3,X2)),X1)=k1_wellord1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_wellord1)).
% 3.47/3.65  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)))))), inference(assume_negation,[status(cth)],[t37_wellord1])).
% 3.47/3.65  fof(c_0_12, plain, ![X27, X28]:((~v1_relat_2(X27)|(~r2_hidden(X28,k3_relat_1(X27))|r2_hidden(k4_tarski(X28,X28),X27))|~v1_relat_1(X27))&((r2_hidden(esk3_1(X27),k3_relat_1(X27))|v1_relat_2(X27)|~v1_relat_1(X27))&(~r2_hidden(k4_tarski(esk3_1(X27),esk3_1(X27)),X27)|v1_relat_2(X27)|~v1_relat_1(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).
% 3.47/3.65  fof(c_0_13, negated_conjecture, (v1_relat_1(esk8_0)&(((v2_wellord1(esk8_0)&r2_hidden(esk6_0,k3_relat_1(esk8_0)))&r2_hidden(esk7_0,k3_relat_1(esk8_0)))&((~r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|~r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)))&(r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 3.47/3.65  fof(c_0_14, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.47/3.65  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X2,X2),X1)|~v1_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 3.47/3.65  cnf(c_0_16, negated_conjecture, (r2_hidden(esk6_0,k3_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.47/3.65  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.47/3.65  fof(c_0_18, plain, ![X24]:((((((v1_relat_2(X24)|~v2_wellord1(X24)|~v1_relat_1(X24))&(v8_relat_2(X24)|~v2_wellord1(X24)|~v1_relat_1(X24)))&(v4_relat_2(X24)|~v2_wellord1(X24)|~v1_relat_1(X24)))&(v6_relat_2(X24)|~v2_wellord1(X24)|~v1_relat_1(X24)))&(v1_wellord1(X24)|~v2_wellord1(X24)|~v1_relat_1(X24)))&(~v1_relat_2(X24)|~v8_relat_2(X24)|~v4_relat_2(X24)|~v6_relat_2(X24)|~v1_wellord1(X24)|v2_wellord1(X24)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 3.47/3.65  cnf(c_0_19, negated_conjecture, (~r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|~r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.47/3.65  cnf(c_0_20, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.47/3.65  cnf(c_0_21, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.47/3.65  cnf(c_0_22, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk6_0),esk8_0)|~v1_relat_2(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 3.47/3.65  cnf(c_0_23, plain, (v1_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.47/3.65  cnf(c_0_24, negated_conjecture, (v2_wellord1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.47/3.65  fof(c_0_25, plain, ![X16, X17, X18, X19, X20, X21, X22]:((((X19!=X17|~r2_hidden(X19,X18)|X18!=k1_wellord1(X16,X17)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(X19,X17),X16)|~r2_hidden(X19,X18)|X18!=k1_wellord1(X16,X17)|~v1_relat_1(X16)))&(X20=X17|~r2_hidden(k4_tarski(X20,X17),X16)|r2_hidden(X20,X18)|X18!=k1_wellord1(X16,X17)|~v1_relat_1(X16)))&((~r2_hidden(esk2_3(X16,X21,X22),X22)|(esk2_3(X16,X21,X22)=X21|~r2_hidden(k4_tarski(esk2_3(X16,X21,X22),X21),X16))|X22=k1_wellord1(X16,X21)|~v1_relat_1(X16))&((esk2_3(X16,X21,X22)!=X21|r2_hidden(esk2_3(X16,X21,X22),X22)|X22=k1_wellord1(X16,X21)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(esk2_3(X16,X21,X22),X21),X16)|r2_hidden(esk2_3(X16,X21,X22),X22)|X22=k1_wellord1(X16,X21)|~v1_relat_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 3.47/3.65  fof(c_0_26, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 3.47/3.65  fof(c_0_27, plain, ![X37, X38]:((r1_tarski(k3_relat_1(k2_wellord1(X38,X37)),k3_relat_1(X38))|~v1_relat_1(X38))&(r1_tarski(k3_relat_1(k2_wellord1(X38,X37)),X37)|~v1_relat_1(X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_wellord1])])])).
% 3.47/3.65  cnf(c_0_28, negated_conjecture, (~r2_hidden(k4_tarski(esk6_0,X1),esk8_0)|~r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,X1))|~r1_tarski(esk7_0,X1)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 3.47/3.65  cnf(c_0_29, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_21])).
% 3.47/3.65  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk6_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_17])])).
% 3.47/3.65  fof(c_0_31, plain, ![X30, X31, X32]:((~v6_relat_2(X30)|(~r2_hidden(X31,k3_relat_1(X30))|~r2_hidden(X32,k3_relat_1(X30))|X31=X32|r2_hidden(k4_tarski(X31,X32),X30)|r2_hidden(k4_tarski(X32,X31),X30))|~v1_relat_1(X30))&(((((r2_hidden(esk4_1(X30),k3_relat_1(X30))|v6_relat_2(X30)|~v1_relat_1(X30))&(r2_hidden(esk5_1(X30),k3_relat_1(X30))|v6_relat_2(X30)|~v1_relat_1(X30)))&(esk4_1(X30)!=esk5_1(X30)|v6_relat_2(X30)|~v1_relat_1(X30)))&(~r2_hidden(k4_tarski(esk4_1(X30),esk5_1(X30)),X30)|v6_relat_2(X30)|~v1_relat_1(X30)))&(~r2_hidden(k4_tarski(esk5_1(X30),esk4_1(X30)),X30)|v6_relat_2(X30)|~v1_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 3.47/3.65  cnf(c_0_32, plain, (X1!=X2|~r2_hidden(X1,X3)|X3!=k1_wellord1(X4,X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.47/3.65  cnf(c_0_33, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.47/3.65  cnf(c_0_34, plain, (r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.47/3.65  fof(c_0_35, plain, ![X35, X36]:(~v1_relat_1(X36)|r1_tarski(k1_wellord1(X36,X35),k3_relat_1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).
% 3.47/3.65  fof(c_0_36, plain, ![X25, X26]:(~v1_relat_1(X25)|v1_relat_1(k2_wellord1(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).
% 3.47/3.65  cnf(c_0_37, negated_conjecture, (~r1_tarski(esk7_0,esk6_0)|~r1_tarski(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 3.47/3.65  cnf(c_0_38, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.47/3.65  cnf(c_0_39, negated_conjecture, (r2_hidden(esk7_0,k3_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.47/3.65  cnf(c_0_40, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).
% 3.47/3.65  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~v1_relat_1(X3)|~r1_tarski(X1,k3_relat_1(k2_wellord1(X3,X2)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 3.47/3.65  cnf(c_0_42, plain, (r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 3.47/3.65  cnf(c_0_43, plain, (v1_relat_1(k2_wellord1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.47/3.65  cnf(c_0_44, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.47/3.65  cnf(c_0_45, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,X1),X2)|r2_hidden(k4_tarski(X1,esk6_0),X2)|~v6_relat_2(X2)|~v1_relat_1(X2)|~r2_hidden(esk6_0,k3_relat_1(X2))|~r2_hidden(X1,k3_relat_1(X2))|~r1_tarski(esk7_0,X1)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 3.47/3.65  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk8_0))|~r1_tarski(esk7_0,X1)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_39, c_0_20])).
% 3.47/3.65  cnf(c_0_47, plain, (~v1_relat_1(X1)|~r2_hidden(X2,X3)|~r1_tarski(k1_wellord1(X1,X2),X3)|~r1_tarski(X3,k1_wellord1(X1,X2))), inference(spm,[status(thm)],[c_0_40, c_0_20])).
% 3.47/3.65  cnf(c_0_48, plain, (r1_tarski(k1_wellord1(k2_wellord1(X1,X2),X3),X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 3.47/3.65  fof(c_0_49, plain, ![X39, X40, X41]:(~v1_relat_1(X41)|(~v2_wellord1(X41)|~r2_hidden(X39,k1_wellord1(X41,X40))|k1_wellord1(k2_wellord1(X41,k1_wellord1(X41,X40)),X39)=k1_wellord1(X41,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_wellord1])])).
% 3.47/3.65  cnf(c_0_50, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(er,[status(thm)],[c_0_44])).
% 3.47/3.65  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(X1,esk6_0),esk8_0)|r2_hidden(k4_tarski(esk6_0,X1),esk8_0)|~v6_relat_2(esk8_0)|~r1_tarski(esk7_0,X1)|~r1_tarski(X1,esk7_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_16]), c_0_17])]), c_0_46])).
% 3.47/3.65  cnf(c_0_52, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.47/3.65  cnf(c_0_53, plain, (~v1_relat_1(X1)|~r2_hidden(X2,X3)|~r1_tarski(X3,k1_wellord1(k2_wellord1(X1,X3),X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_43])).
% 3.47/3.65  cnf(c_0_54, plain, (k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X3)),X2)=k1_wellord1(X1,X2)|~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k1_wellord1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 3.47/3.65  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,k1_wellord1(X2,esk6_0))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,esk6_0),X2)|~r1_tarski(esk7_0,X1)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_50])).
% 3.47/3.65  cnf(c_0_56, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,X1),esk8_0)|r2_hidden(k4_tarski(X1,esk6_0),esk8_0)|~r1_tarski(esk7_0,X1)|~r1_tarski(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_24]), c_0_17])])).
% 3.47/3.65  cnf(c_0_57, plain, (~v2_wellord1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X3))|~r1_tarski(k1_wellord1(X1,X3),k1_wellord1(X1,X2))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 3.47/3.65  cnf(c_0_58, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.47/3.65  cnf(c_0_59, negated_conjecture, (r2_hidden(esk6_0,k1_wellord1(X1,X2))|~v1_relat_1(X1)|~r2_hidden(k4_tarski(esk6_0,X2),X1)|~r1_tarski(esk7_0,X2)|~r1_tarski(X2,esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_50])).
% 3.47/3.65  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k1_wellord1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X3),X2)|~r1_tarski(esk7_0,X1)|~r1_tarski(X1,esk7_0)|~r1_tarski(X3,esk6_0)|~r1_tarski(esk6_0,X3)), inference(spm,[status(thm)],[c_0_55, c_0_20])).
% 3.47/3.65  cnf(c_0_61, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk6_0),esk8_0)|r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_29]), c_0_29])])).
% 3.47/3.65  cnf(c_0_62, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|~r2_hidden(esk7_0,k1_wellord1(esk8_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_24]), c_0_17])])).
% 3.47/3.65  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,k1_wellord1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X3),X2)|~r1_tarski(esk7_0,X3)|~r1_tarski(X3,esk7_0)|~r1_tarski(X1,esk6_0)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_20])).
% 3.47/3.65  cnf(c_0_64, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_17]), c_0_29]), c_0_29])]), c_0_62])).
% 3.47/3.65  cnf(c_0_65, plain, (r1_tarski(k1_wellord1(X1,X2),k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X3))))|~v2_wellord1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_54]), c_0_43])).
% 3.47/3.65  cnf(c_0_66, negated_conjecture, (r2_hidden(esk6_0,k1_wellord1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_17]), c_0_29]), c_0_29])])).
% 3.47/3.65  cnf(c_0_67, negated_conjecture, (r1_tarski(k1_wellord1(esk8_0,esk6_0),k3_relat_1(k2_wellord1(esk8_0,k1_wellord1(esk8_0,esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_24]), c_0_17])])).
% 3.47/3.65  cnf(c_0_68, negated_conjecture, (~r1_tarski(k1_wellord1(esk8_0,esk6_0),k1_wellord1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_64])])).
% 3.47/3.65  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_67]), c_0_17])]), c_0_68]), ['proof']).
% 3.47/3.65  # SZS output end CNFRefutation
% 3.47/3.65  # Proof object total steps             : 70
% 3.47/3.65  # Proof object clause steps            : 47
% 3.47/3.65  # Proof object formula steps           : 23
% 3.47/3.65  # Proof object conjectures             : 28
% 3.47/3.65  # Proof object clause conjectures      : 25
% 3.47/3.65  # Proof object formula conjectures     : 3
% 3.47/3.65  # Proof object initial clauses used    : 19
% 3.47/3.65  # Proof object initial formulas used   : 11
% 3.47/3.65  # Proof object generating inferences   : 24
% 3.47/3.65  # Proof object simplifying inferences  : 42
% 3.47/3.65  # Training examples: 0 positive, 0 negative
% 3.47/3.65  # Parsed axioms                        : 12
% 3.47/3.65  # Removed by relevancy pruning/SinE    : 0
% 3.47/3.65  # Initial clauses                      : 39
% 3.47/3.65  # Removed in clause preprocessing      : 0
% 3.47/3.65  # Initial clauses in saturation        : 39
% 3.47/3.65  # Processed clauses                    : 9720
% 3.47/3.65  # ...of these trivial                  : 25
% 3.47/3.65  # ...subsumed                          : 6321
% 3.47/3.65  # ...remaining for further processing  : 3374
% 3.47/3.65  # Other redundant clauses eliminated   : 35
% 3.47/3.65  # Clauses deleted for lack of memory   : 0
% 3.47/3.65  # Backward-subsumed                    : 554
% 3.47/3.65  # Backward-rewritten                   : 826
% 3.47/3.65  # Generated clauses                    : 228308
% 3.47/3.65  # ...of the previous two non-trivial   : 222334
% 3.47/3.65  # Contextual simplify-reflections      : 64
% 3.47/3.65  # Paramodulations                      : 227940
% 3.47/3.65  # Factorizations                       : 334
% 3.47/3.65  # Equation resolutions                 : 35
% 3.47/3.65  # Propositional unsat checks           : 0
% 3.47/3.65  #    Propositional check models        : 0
% 3.47/3.65  #    Propositional check unsatisfiable : 0
% 3.47/3.65  #    Propositional clauses             : 0
% 3.47/3.65  #    Propositional clauses after purity: 0
% 3.47/3.65  #    Propositional unsat core size     : 0
% 3.47/3.65  #    Propositional preprocessing time  : 0.000
% 3.47/3.65  #    Propositional encoding time       : 0.000
% 3.47/3.65  #    Propositional solver time         : 0.000
% 3.47/3.65  #    Success case prop preproc time    : 0.000
% 3.47/3.65  #    Success case prop encoding time   : 0.000
% 3.47/3.65  #    Success case prop solver time     : 0.000
% 3.47/3.65  # Current number of processed clauses  : 1951
% 3.47/3.65  #    Positive orientable unit clauses  : 53
% 3.47/3.65  #    Positive unorientable unit clauses: 0
% 3.47/3.65  #    Negative unit clauses             : 19
% 3.47/3.65  #    Non-unit-clauses                  : 1879
% 3.47/3.65  # Current number of unprocessed clauses: 211891
% 3.47/3.65  # ...number of literals in the above   : 1735791
% 3.47/3.65  # Current number of archived formulas  : 0
% 3.47/3.65  # Current number of archived clauses   : 1418
% 3.47/3.65  # Clause-clause subsumption calls (NU) : 1400124
% 3.47/3.65  # Rec. Clause-clause subsumption calls : 105100
% 3.47/3.65  # Non-unit clause-clause subsumptions  : 6564
% 3.47/3.65  # Unit Clause-clause subsumption calls : 4434
% 3.47/3.65  # Rewrite failures with RHS unbound    : 0
% 3.47/3.65  # BW rewrite match attempts            : 576
% 3.47/3.65  # BW rewrite match successes           : 15
% 3.47/3.65  # Condensation attempts                : 0
% 3.47/3.65  # Condensation successes               : 0
% 3.47/3.65  # Termbank termtop insertions          : 6487278
% 3.47/3.66  
% 3.47/3.66  # -------------------------------------------------
% 3.47/3.66  # User time                : 3.201 s
% 3.47/3.66  # System time              : 0.120 s
% 3.47/3.66  # Total time               : 3.321 s
% 3.47/3.66  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
