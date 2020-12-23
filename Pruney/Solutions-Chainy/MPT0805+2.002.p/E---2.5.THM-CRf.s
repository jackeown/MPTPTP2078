%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 454 expanded)
%              Number of clauses        :   37 ( 164 expanded)
%              Number of leaves         :   12 ( 111 expanded)
%              Depth                    :   14
%              Number of atoms          :  286 (2258 expanded)
%              Number of equality atoms :   35 ( 363 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ~ ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3))
          & X1 != X2
          & r4_wellord1(k2_wellord1(X3,k1_wellord1(X3,X1)),k2_wellord1(X3,k1_wellord1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_wellord1)).

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

fof(t57_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(t29_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k2_wellord1(k2_wellord1(X3,X2),X1) = k2_wellord1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

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

fof(t35_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k1_wellord1(X3,X2)) )
       => k1_wellord1(k2_wellord1(X3,k1_wellord1(X3,X2)),X1) = k1_wellord1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_wellord1)).

fof(t32_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => v2_wellord1(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

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

fof(t40_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1))) = k1_wellord1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).

fof(t38_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) )
       => ( r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))
        <=> ( X1 = X2
            | r2_hidden(X1,k1_wellord1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ~ ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3))
            & X1 != X2
            & r4_wellord1(k2_wellord1(X3,k1_wellord1(X3,X1)),k2_wellord1(X3,k1_wellord1(X3,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t58_wellord1])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v2_wellord1(esk6_0)
    & r2_hidden(esk4_0,k3_relat_1(esk6_0))
    & r2_hidden(esk5_0,k3_relat_1(esk6_0))
    & esk4_0 != esk5_0
    & r4_wellord1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0)),k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v6_relat_2(X16)
        | ~ r2_hidden(X17,k3_relat_1(X16))
        | ~ r2_hidden(X18,k3_relat_1(X16))
        | X17 = X18
        | r2_hidden(k4_tarski(X17,X18),X16)
        | r2_hidden(k4_tarski(X18,X17),X16)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk2_1(X16),k3_relat_1(X16))
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk3_1(X16),k3_relat_1(X16))
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) )
      & ( esk2_1(X16) != esk3_1(X16)
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk2_1(X16),esk3_1(X16)),X16)
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X16),esk2_1(X16)),X16)
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

fof(c_0_15,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X36)
      | ~ v2_wellord1(X36)
      | ~ r2_hidden(X37,k3_relat_1(X36))
      | ~ r4_wellord1(X36,k2_wellord1(X36,k1_wellord1(X36,X37))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

fof(c_0_16,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ r1_tarski(X21,X22)
      | k2_wellord1(k2_wellord1(X23,X22),X21) = k2_wellord1(X23,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_wellord1])])).

fof(c_0_17,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | v1_relat_1(k2_wellord1(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

fof(c_0_18,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11] :
      ( ( X8 != X6
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(X8,X6),X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( X9 = X6
        | ~ r2_hidden(k4_tarski(X9,X6),X5)
        | r2_hidden(X9,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(esk1_3(X5,X10,X11),X11)
        | esk1_3(X5,X10,X11) = X10
        | ~ r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( esk1_3(X5,X10,X11) != X10
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_wellord1(k2_wellord1(X1,X3),X2) = k2_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ v2_wellord1(X28)
      | ~ r2_hidden(X26,k1_wellord1(X28,X27))
      | k1_wellord1(k2_wellord1(X28,k1_wellord1(X28,X27)),X26) = k1_wellord1(X28,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_wellord1])])).

fof(c_0_25,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v2_wellord1(X25)
      | v2_wellord1(k2_wellord1(X25,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_wellord1])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk5_0),X1)
    | r2_hidden(k4_tarski(esk5_0,esk4_0),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(esk5_0,k3_relat_1(X1))
    | ~ r2_hidden(esk4_0,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk5_0,k3_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_0,k3_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_31,plain,(
    ! [X13] :
      ( ( v1_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v8_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v4_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v6_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v1_wellord1(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( ~ v1_relat_2(X13)
        | ~ v8_relat_2(X13)
        | ~ v4_relat_2(X13)
        | ~ v6_relat_2(X13)
        | ~ v1_wellord1(X13)
        | v2_wellord1(X13)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

cnf(c_0_32,plain,
    ( ~ r4_wellord1(k2_wellord1(X1,X2),k2_wellord1(X1,k1_wellord1(k2_wellord1(X1,X2),X3)))
    | ~ r1_tarski(k1_wellord1(k2_wellord1(X1,X2),X3),X2)
    | ~ v2_wellord1(k2_wellord1(X1,X2))
    | ~ r2_hidden(X3,k3_relat_1(k2_wellord1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_33,plain,
    ( k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X3)),X2) = k1_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk4_0),esk6_0)
    | r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
    | ~ v6_relat_2(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_37,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v2_wellord1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,plain,
    ( ~ r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,k1_wellord1(X1,X3)))
    | ~ r1_tarski(k1_wellord1(X1,X3),k1_wellord1(X1,X2))
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X3,k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2))))
    | ~ r2_hidden(X3,k1_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r4_wellord1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0)),k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_41,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ v2_wellord1(X33)
      | k3_relat_1(k2_wellord1(X33,k1_wellord1(X33,X32))) = k1_wellord1(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_wellord1])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_0,k1_wellord1(X1,esk4_0))
    | ~ r2_hidden(k4_tarski(esk5_0,esk4_0),X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_35])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
    | r2_hidden(k4_tarski(esk5_0,esk4_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_30])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk6_0,esk5_0),k1_wellord1(esk6_0,esk4_0))
    | ~ r2_hidden(esk5_0,k3_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0))))
    | ~ r2_hidden(esk5_0,k1_wellord1(esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_38]),c_0_30])])).

cnf(c_0_45,plain,
    ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2))) = k1_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_46,plain,(
    ! [X29,X30,X31] :
      ( ( ~ r1_tarski(k1_wellord1(X31,X29),k1_wellord1(X31,X30))
        | X29 = X30
        | r2_hidden(X29,k1_wellord1(X31,X30))
        | ~ v2_wellord1(X31)
        | ~ r2_hidden(X29,k3_relat_1(X31))
        | ~ r2_hidden(X30,k3_relat_1(X31))
        | ~ v1_relat_1(X31) )
      & ( X29 != X30
        | r1_tarski(k1_wellord1(X31,X29),k1_wellord1(X31,X30))
        | ~ v2_wellord1(X31)
        | ~ r2_hidden(X29,k3_relat_1(X31))
        | ~ r2_hidden(X30,k3_relat_1(X31))
        | ~ v1_relat_1(X31) )
      & ( ~ r2_hidden(X29,k1_wellord1(X31,X30))
        | r1_tarski(k1_wellord1(X31,X29),k1_wellord1(X31,X30))
        | ~ v2_wellord1(X31)
        | ~ r2_hidden(X29,k3_relat_1(X31))
        | ~ r2_hidden(X30,k3_relat_1(X31))
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_wellord1])])])).

fof(c_0_47,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X34)
      | ~ v1_relat_1(X35)
      | ~ r4_wellord1(X34,X35)
      | r4_wellord1(X35,X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_0,k1_wellord1(X1,esk5_0))
    | ~ r2_hidden(k4_tarski(esk4_0,esk5_0),X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_35])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)
    | r2_hidden(esk5_0,k1_wellord1(esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_30])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk6_0,esk5_0),k1_wellord1(esk6_0,esk4_0))
    | ~ r2_hidden(esk5_0,k1_wellord1(esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_38]),c_0_30])])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_wellord1(X2,X1),k1_wellord1(X2,X3))
    | ~ r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ v2_wellord1(X2)
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X3,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk5_0,k1_wellord1(esk6_0,esk4_0))
    | r2_hidden(esk4_0,k1_wellord1(esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_30])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_wellord1(esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_38]),c_0_29]),c_0_28]),c_0_30])])).

cnf(c_0_55,negated_conjecture,
    ( r4_wellord1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0)),k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0)))
    | ~ v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0)))
    | ~ v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk4_0,k1_wellord1(esk6_0,esk5_0)) ),
    inference(sr,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk6_0,esk4_0),k1_wellord1(esk6_0,esk5_0))
    | ~ r2_hidden(esk4_0,k3_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0))))
    | ~ v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0)))
    | ~ v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_55]),c_0_38]),c_0_30])]),c_0_56])])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(esk6_0,esk4_0),k1_wellord1(esk6_0,esk5_0))
    | ~ v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0)))
    | ~ v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_45]),c_0_56]),c_0_38]),c_0_30])])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0)))
    | ~ v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_51]),c_0_38]),c_0_56]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_23]),c_0_30])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_23]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.20/0.43  # and selection function PSelectUnlessUniqMaxPos.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.032 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t58_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>~(((((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))&X1!=X2)&r4_wellord1(k2_wellord1(X3,k1_wellord1(X3,X1)),k2_wellord1(X3,k1_wellord1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_wellord1)).
% 0.20/0.43  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l4_wellord1)).
% 0.20/0.43  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 0.20/0.43  fof(t29_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k2_wellord1(k2_wellord1(X3,X2),X1)=k2_wellord1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord1)).
% 0.20/0.43  fof(dt_k2_wellord1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k2_wellord1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 0.20/0.43  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 0.20/0.43  fof(t35_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((v2_wellord1(X3)&r2_hidden(X1,k1_wellord1(X3,X2)))=>k1_wellord1(k2_wellord1(X3,k1_wellord1(X3,X2)),X1)=k1_wellord1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_wellord1)).
% 0.20/0.43  fof(t32_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v2_wellord1(X2)=>v2_wellord1(k2_wellord1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_wellord1)).
% 0.20/0.43  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 0.20/0.43  fof(t40_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v2_wellord1(X2)=>k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1)))=k1_wellord1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_wellord1)).
% 0.20/0.43  fof(t38_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))<=>(X1=X2|r2_hidden(X1,k1_wellord1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_wellord1)).
% 0.20/0.43  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 0.20/0.43  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>~(((((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))&X1!=X2)&r4_wellord1(k2_wellord1(X3,k1_wellord1(X3,X1)),k2_wellord1(X3,k1_wellord1(X3,X2))))))), inference(assume_negation,[status(cth)],[t58_wellord1])).
% 0.20/0.43  fof(c_0_13, negated_conjecture, (v1_relat_1(esk6_0)&((((v2_wellord1(esk6_0)&r2_hidden(esk4_0,k3_relat_1(esk6_0)))&r2_hidden(esk5_0,k3_relat_1(esk6_0)))&esk4_0!=esk5_0)&r4_wellord1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0)),k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.43  fof(c_0_14, plain, ![X16, X17, X18]:((~v6_relat_2(X16)|(~r2_hidden(X17,k3_relat_1(X16))|~r2_hidden(X18,k3_relat_1(X16))|X17=X18|r2_hidden(k4_tarski(X17,X18),X16)|r2_hidden(k4_tarski(X18,X17),X16))|~v1_relat_1(X16))&(((((r2_hidden(esk2_1(X16),k3_relat_1(X16))|v6_relat_2(X16)|~v1_relat_1(X16))&(r2_hidden(esk3_1(X16),k3_relat_1(X16))|v6_relat_2(X16)|~v1_relat_1(X16)))&(esk2_1(X16)!=esk3_1(X16)|v6_relat_2(X16)|~v1_relat_1(X16)))&(~r2_hidden(k4_tarski(esk2_1(X16),esk3_1(X16)),X16)|v6_relat_2(X16)|~v1_relat_1(X16)))&(~r2_hidden(k4_tarski(esk3_1(X16),esk2_1(X16)),X16)|v6_relat_2(X16)|~v1_relat_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.20/0.43  fof(c_0_15, plain, ![X36, X37]:(~v1_relat_1(X36)|(~v2_wellord1(X36)|(~r2_hidden(X37,k3_relat_1(X36))|~r4_wellord1(X36,k2_wellord1(X36,k1_wellord1(X36,X37)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.20/0.43  fof(c_0_16, plain, ![X21, X22, X23]:(~v1_relat_1(X23)|(~r1_tarski(X21,X22)|k2_wellord1(k2_wellord1(X23,X22),X21)=k2_wellord1(X23,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_wellord1])])).
% 0.20/0.43  fof(c_0_17, plain, ![X14, X15]:(~v1_relat_1(X14)|v1_relat_1(k2_wellord1(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).
% 0.20/0.43  fof(c_0_18, plain, ![X5, X6, X7, X8, X9, X10, X11]:((((X8!=X6|~r2_hidden(X8,X7)|X7!=k1_wellord1(X5,X6)|~v1_relat_1(X5))&(r2_hidden(k4_tarski(X8,X6),X5)|~r2_hidden(X8,X7)|X7!=k1_wellord1(X5,X6)|~v1_relat_1(X5)))&(X9=X6|~r2_hidden(k4_tarski(X9,X6),X5)|r2_hidden(X9,X7)|X7!=k1_wellord1(X5,X6)|~v1_relat_1(X5)))&((~r2_hidden(esk1_3(X5,X10,X11),X11)|(esk1_3(X5,X10,X11)=X10|~r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5))|X11=k1_wellord1(X5,X10)|~v1_relat_1(X5))&((esk1_3(X5,X10,X11)!=X10|r2_hidden(esk1_3(X5,X10,X11),X11)|X11=k1_wellord1(X5,X10)|~v1_relat_1(X5))&(r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)|r2_hidden(esk1_3(X5,X10,X11),X11)|X11=k1_wellord1(X5,X10)|~v1_relat_1(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.20/0.43  cnf(c_0_19, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_20, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_21, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_22, plain, (k2_wellord1(k2_wellord1(X1,X3),X2)=k2_wellord1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_23, plain, (v1_relat_1(k2_wellord1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  fof(c_0_24, plain, ![X26, X27, X28]:(~v1_relat_1(X28)|(~v2_wellord1(X28)|~r2_hidden(X26,k1_wellord1(X28,X27))|k1_wellord1(k2_wellord1(X28,k1_wellord1(X28,X27)),X26)=k1_wellord1(X28,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_wellord1])])).
% 0.20/0.43  fof(c_0_25, plain, ![X24, X25]:(~v1_relat_1(X25)|(~v2_wellord1(X25)|v2_wellord1(k2_wellord1(X25,X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_wellord1])])).
% 0.20/0.43  cnf(c_0_26, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.43  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,esk5_0),X1)|r2_hidden(k4_tarski(esk5_0,esk4_0),X1)|~v6_relat_2(X1)|~r2_hidden(esk5_0,k3_relat_1(X1))|~r2_hidden(esk4_0,k3_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20])])).
% 0.20/0.43  cnf(c_0_28, negated_conjecture, (r2_hidden(esk5_0,k3_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_29, negated_conjecture, (r2_hidden(esk4_0,k3_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  fof(c_0_31, plain, ![X13]:((((((v1_relat_2(X13)|~v2_wellord1(X13)|~v1_relat_1(X13))&(v8_relat_2(X13)|~v2_wellord1(X13)|~v1_relat_1(X13)))&(v4_relat_2(X13)|~v2_wellord1(X13)|~v1_relat_1(X13)))&(v6_relat_2(X13)|~v2_wellord1(X13)|~v1_relat_1(X13)))&(v1_wellord1(X13)|~v2_wellord1(X13)|~v1_relat_1(X13)))&(~v1_relat_2(X13)|~v8_relat_2(X13)|~v4_relat_2(X13)|~v6_relat_2(X13)|~v1_wellord1(X13)|v2_wellord1(X13)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.20/0.43  cnf(c_0_32, plain, (~r4_wellord1(k2_wellord1(X1,X2),k2_wellord1(X1,k1_wellord1(k2_wellord1(X1,X2),X3)))|~r1_tarski(k1_wellord1(k2_wellord1(X1,X2),X3),X2)|~v2_wellord1(k2_wellord1(X1,X2))|~r2_hidden(X3,k3_relat_1(k2_wellord1(X1,X2)))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.20/0.43  cnf(c_0_33, plain, (k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X3)),X2)=k1_wellord1(X1,X2)|~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k1_wellord1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_34, plain, (v2_wellord1(k2_wellord1(X1,X2))|~v1_relat_1(X1)|~v2_wellord1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.43  cnf(c_0_35, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_26])).
% 0.20/0.43  cnf(c_0_36, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,esk4_0),esk6_0)|r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|~v6_relat_2(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])])).
% 0.20/0.43  cnf(c_0_37, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.43  cnf(c_0_38, negated_conjecture, (v2_wellord1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_39, plain, (~r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,k1_wellord1(X1,X3)))|~r1_tarski(k1_wellord1(X1,X3),k1_wellord1(X1,X2))|~v2_wellord1(X1)|~r2_hidden(X3,k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2))))|~r2_hidden(X3,k1_wellord1(X1,X2))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (r4_wellord1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0)),k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  fof(c_0_41, plain, ![X32, X33]:(~v1_relat_1(X33)|(~v2_wellord1(X33)|k3_relat_1(k2_wellord1(X33,k1_wellord1(X33,X32)))=k1_wellord1(X33,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_wellord1])])).
% 0.20/0.43  cnf(c_0_42, negated_conjecture, (r2_hidden(esk5_0,k1_wellord1(X1,esk4_0))|~r2_hidden(k4_tarski(esk5_0,esk4_0),X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_35])])).
% 0.20/0.43  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|r2_hidden(k4_tarski(esk5_0,esk4_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_30])])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (~r1_tarski(k1_wellord1(esk6_0,esk5_0),k1_wellord1(esk6_0,esk4_0))|~r2_hidden(esk5_0,k3_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0))))|~r2_hidden(esk5_0,k1_wellord1(esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_38]), c_0_30])])).
% 0.20/0.43  cnf(c_0_45, plain, (k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2)))=k1_wellord1(X1,X2)|~v1_relat_1(X1)|~v2_wellord1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.43  fof(c_0_46, plain, ![X29, X30, X31]:((~r1_tarski(k1_wellord1(X31,X29),k1_wellord1(X31,X30))|(X29=X30|r2_hidden(X29,k1_wellord1(X31,X30)))|(~v2_wellord1(X31)|~r2_hidden(X29,k3_relat_1(X31))|~r2_hidden(X30,k3_relat_1(X31)))|~v1_relat_1(X31))&((X29!=X30|r1_tarski(k1_wellord1(X31,X29),k1_wellord1(X31,X30))|(~v2_wellord1(X31)|~r2_hidden(X29,k3_relat_1(X31))|~r2_hidden(X30,k3_relat_1(X31)))|~v1_relat_1(X31))&(~r2_hidden(X29,k1_wellord1(X31,X30))|r1_tarski(k1_wellord1(X31,X29),k1_wellord1(X31,X30))|(~v2_wellord1(X31)|~r2_hidden(X29,k3_relat_1(X31))|~r2_hidden(X30,k3_relat_1(X31)))|~v1_relat_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_wellord1])])])).
% 0.20/0.43  fof(c_0_47, plain, ![X34, X35]:(~v1_relat_1(X34)|(~v1_relat_1(X35)|(~r4_wellord1(X34,X35)|r4_wellord1(X35,X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.20/0.43  cnf(c_0_48, negated_conjecture, (r2_hidden(esk4_0,k1_wellord1(X1,esk5_0))|~r2_hidden(k4_tarski(esk4_0,esk5_0),X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_35])])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)|r2_hidden(esk5_0,k1_wellord1(esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_30])])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (~r1_tarski(k1_wellord1(esk6_0,esk5_0),k1_wellord1(esk6_0,esk4_0))|~r2_hidden(esk5_0,k1_wellord1(esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_38]), c_0_30])])).
% 0.20/0.43  cnf(c_0_51, plain, (r1_tarski(k1_wellord1(X2,X1),k1_wellord1(X2,X3))|~r2_hidden(X1,k1_wellord1(X2,X3))|~v2_wellord1(X2)|~r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(X3,k3_relat_1(X2))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.43  cnf(c_0_52, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (r2_hidden(esk5_0,k1_wellord1(esk6_0,esk4_0))|r2_hidden(esk4_0,k1_wellord1(esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_30])])).
% 0.20/0.43  cnf(c_0_54, negated_conjecture, (~r2_hidden(esk5_0,k1_wellord1(esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_38]), c_0_29]), c_0_28]), c_0_30])])).
% 0.20/0.43  cnf(c_0_55, negated_conjecture, (r4_wellord1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0)),k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0)))|~v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0)))|~v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0)))), inference(spm,[status(thm)],[c_0_52, c_0_40])).
% 0.20/0.43  cnf(c_0_56, negated_conjecture, (r2_hidden(esk4_0,k1_wellord1(esk6_0,esk5_0))), inference(sr,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.43  cnf(c_0_57, negated_conjecture, (~r1_tarski(k1_wellord1(esk6_0,esk4_0),k1_wellord1(esk6_0,esk5_0))|~r2_hidden(esk4_0,k3_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0))))|~v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0)))|~v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_55]), c_0_38]), c_0_30])]), c_0_56])])).
% 0.20/0.43  cnf(c_0_58, negated_conjecture, (~r1_tarski(k1_wellord1(esk6_0,esk4_0),k1_wellord1(esk6_0,esk5_0))|~v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0)))|~v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_45]), c_0_56]), c_0_38]), c_0_30])])).
% 0.20/0.43  cnf(c_0_59, negated_conjecture, (~v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk5_0)))|~v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_51]), c_0_38]), c_0_56]), c_0_28]), c_0_29]), c_0_30])])).
% 0.20/0.43  cnf(c_0_60, negated_conjecture, (~v1_relat_1(k2_wellord1(esk6_0,k1_wellord1(esk6_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_23]), c_0_30])])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_23]), c_0_30])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 62
% 0.20/0.43  # Proof object clause steps            : 37
% 0.20/0.43  # Proof object formula steps           : 25
% 0.20/0.43  # Proof object conjectures             : 26
% 0.20/0.43  # Proof object clause conjectures      : 23
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 17
% 0.20/0.43  # Proof object initial formulas used   : 12
% 0.20/0.43  # Proof object generating inferences   : 18
% 0.20/0.43  # Proof object simplifying inferences  : 47
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 12
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 34
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 34
% 0.20/0.43  # Processed clauses                    : 141
% 0.20/0.43  # ...of these trivial                  : 0
% 0.20/0.43  # ...subsumed                          : 6
% 0.20/0.43  # ...remaining for further processing  : 135
% 0.20/0.43  # Other redundant clauses eliminated   : 30
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 5
% 0.20/0.43  # Backward-rewritten                   : 3
% 0.20/0.43  # Generated clauses                    : 2608
% 0.20/0.43  # ...of the previous two non-trivial   : 2558
% 0.20/0.43  # Contextual simplify-reflections      : 3
% 0.20/0.43  # Paramodulations                      : 2577
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 30
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 87
% 0.20/0.43  #    Positive orientable unit clauses  : 7
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 3
% 0.20/0.43  #    Non-unit-clauses                  : 77
% 0.20/0.43  # Current number of unprocessed clauses: 2448
% 0.20/0.43  # ...number of literals in the above   : 20693
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 44
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 1348
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 349
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 14
% 0.20/0.43  # Unit Clause-clause subsumption calls : 68
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 2
% 0.20/0.43  # BW rewrite match successes           : 2
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 66579
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.089 s
% 0.20/0.43  # System time              : 0.003 s
% 0.20/0.43  # Total time               : 0.092 s
% 0.20/0.43  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
