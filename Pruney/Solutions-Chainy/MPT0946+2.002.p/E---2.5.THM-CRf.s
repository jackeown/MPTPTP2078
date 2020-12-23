%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:42 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 320 expanded)
%              Number of clauses        :   41 ( 129 expanded)
%              Number of leaves         :   14 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  223 (1054 expanded)
%              Number of equality atoms :   42 ( 220 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
           => X1 = k1_wellord1(k1_wellord2(X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(t11_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(t7_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v2_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t50_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_xboole_0(X1,X2)
              & X1 != X2
              & ~ r2_xboole_0(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).

fof(t57_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t8_wellord2,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_14,plain,(
    ! [X27,X28] :
      ( ~ v3_ordinal1(X27)
      | ~ v3_ordinal1(X28)
      | ~ r2_hidden(X27,X28)
      | X27 = k1_wellord1(k1_wellord2(X28),X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

fof(c_0_15,plain,(
    ! [X12,X13] :
      ( ~ v3_ordinal1(X13)
      | ~ r2_hidden(X12,X13)
      | v3_ordinal1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord2])).

cnf(c_0_17,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    & v3_ordinal1(esk4_0)
    & r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0))
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X29] :
      ( ~ v3_ordinal1(X29)
      | v2_wellord1(k1_wellord2(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).

fof(c_0_21,plain,(
    ! [X20,X21,X22,X23] :
      ( ( k3_relat_1(X21) = X20
        | X21 != k1_wellord2(X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(X22,X23),X21)
        | r1_tarski(X22,X23)
        | ~ r2_hidden(X22,X20)
        | ~ r2_hidden(X23,X20)
        | X21 != k1_wellord2(X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r1_tarski(X22,X23)
        | r2_hidden(k4_tarski(X22,X23),X21)
        | ~ r2_hidden(X22,X20)
        | ~ r2_hidden(X23,X20)
        | X21 != k1_wellord2(X20)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk1_2(X20,X21),X20)
        | k3_relat_1(X21) != X20
        | X21 = k1_wellord2(X20)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk2_2(X20,X21),X20)
        | k3_relat_1(X21) != X20
        | X21 = k1_wellord2(X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X20,X21),esk2_2(X20,X21)),X21)
        | ~ r1_tarski(esk1_2(X20,X21),esk2_2(X20,X21))
        | k3_relat_1(X21) != X20
        | X21 = k1_wellord2(X20)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk1_2(X20,X21),esk2_2(X20,X21)),X21)
        | r1_tarski(esk1_2(X20,X21),esk2_2(X20,X21))
        | k3_relat_1(X21) != X20
        | X21 = k1_wellord2(X20)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_22,plain,(
    ! [X26] : v1_relat_1(k1_wellord2(X26)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_23,plain,(
    ! [X14,X15] :
      ( ~ v3_ordinal1(X14)
      | ~ v3_ordinal1(X15)
      | r2_xboole_0(X14,X15)
      | X14 = X15
      | r2_xboole_0(X15,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_ordinal1])])])])).

fof(c_0_24,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v2_wellord1(X18)
      | ~ r2_hidden(X19,k3_relat_1(X18))
      | ~ r4_wellord1(X18,k2_wellord1(X18,k1_wellord1(X18,X19))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

cnf(c_0_25,plain,
    ( k1_wellord1(k1_wellord2(X1),X2) = X2
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r2_xboole_0(X1,X2)
    | X1 = X2
    | r2_xboole_0(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X9] :
      ( ( v1_ordinal1(X9)
        | ~ v3_ordinal1(X9) )
      & ( v2_ordinal1(X9)
        | ~ v3_ordinal1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_32,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk4_0),X1) = X1
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_35,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])])).

fof(c_0_36,plain,(
    ! [X30,X31] :
      ( ~ r1_tarski(X30,X31)
      | k2_wellord1(k1_wellord2(X31),X30) = k1_wellord2(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

fof(c_0_37,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | ~ r4_wellord1(X16,X17)
      | r4_wellord1(X17,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

fof(c_0_38,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | ~ r2_xboole_0(X5,X6) )
      & ( X5 != X6
        | ~ r2_xboole_0(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | X5 = X6
        | r2_xboole_0(X5,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_39,negated_conjecture,
    ( X1 = esk4_0
    | r2_xboole_0(X1,esk4_0)
    | r2_xboole_0(esk4_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_42,plain,(
    ! [X10,X11] :
      ( ~ v1_ordinal1(X10)
      | ~ v3_ordinal1(X11)
      | ~ r2_xboole_0(X10,X11)
      | r2_hidden(X10,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

cnf(c_0_43,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),X1))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_29]),c_0_35])])).

cnf(c_0_45,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( r2_xboole_0(esk4_0,esk3_0)
    | r2_xboole_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v1_ordinal1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(X1))
    | ~ r2_hidden(X1,esk4_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_29]),c_0_29])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r2_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_xboole_0(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_49]),c_0_51]),c_0_26])])).

fof(c_0_56,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_57,negated_conjecture,
    ( v1_ordinal1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0)
    | ~ r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk3_0),X1) = X1
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_40])).

cnf(c_0_62,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_40])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_54]),c_0_57]),c_0_40])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk3_0),k2_wellord1(k1_wellord2(esk3_0),X1))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_61]),c_0_62]),c_0_29]),c_0_35])])).

cnf(c_0_67,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk3_0),k2_wellord1(k1_wellord2(X1),esk4_0))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_45])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_41]),c_0_65])])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t10_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>X1=k1_wellord1(k1_wellord2(X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 0.20/0.38  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.20/0.38  fof(t11_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 0.20/0.38  fof(t7_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 0.20/0.38  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 0.20/0.38  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.20/0.38  fof(t50_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_xboole_0(X1,X2))&X1!=X2)&~(r2_xboole_0(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_ordinal1)).
% 0.20/0.38  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 0.20/0.38  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.20/0.38  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 0.20/0.38  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 0.20/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.38  fof(t21_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_xboole_0(X1,X2)=>r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(c_0_14, plain, ![X27, X28]:(~v3_ordinal1(X27)|(~v3_ordinal1(X28)|(~r2_hidden(X27,X28)|X27=k1_wellord1(k1_wellord2(X28),X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).
% 0.20/0.38  fof(c_0_15, plain, ![X12, X13]:(~v3_ordinal1(X13)|(~r2_hidden(X12,X13)|v3_ordinal1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.20/0.38  fof(c_0_16, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2)))), inference(assume_negation,[status(cth)],[t11_wellord2])).
% 0.20/0.38  cnf(c_0_17, plain, (X1=k1_wellord1(k1_wellord2(X2),X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_18, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  fof(c_0_19, negated_conjecture, (v3_ordinal1(esk3_0)&(v3_ordinal1(esk4_0)&(r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0))&esk3_0!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.38  fof(c_0_20, plain, ![X29]:(~v3_ordinal1(X29)|v2_wellord1(k1_wellord2(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).
% 0.20/0.38  fof(c_0_21, plain, ![X20, X21, X22, X23]:(((k3_relat_1(X21)=X20|X21!=k1_wellord2(X20)|~v1_relat_1(X21))&((~r2_hidden(k4_tarski(X22,X23),X21)|r1_tarski(X22,X23)|(~r2_hidden(X22,X20)|~r2_hidden(X23,X20))|X21!=k1_wellord2(X20)|~v1_relat_1(X21))&(~r1_tarski(X22,X23)|r2_hidden(k4_tarski(X22,X23),X21)|(~r2_hidden(X22,X20)|~r2_hidden(X23,X20))|X21!=k1_wellord2(X20)|~v1_relat_1(X21))))&(((r2_hidden(esk1_2(X20,X21),X20)|k3_relat_1(X21)!=X20|X21=k1_wellord2(X20)|~v1_relat_1(X21))&(r2_hidden(esk2_2(X20,X21),X20)|k3_relat_1(X21)!=X20|X21=k1_wellord2(X20)|~v1_relat_1(X21)))&((~r2_hidden(k4_tarski(esk1_2(X20,X21),esk2_2(X20,X21)),X21)|~r1_tarski(esk1_2(X20,X21),esk2_2(X20,X21))|k3_relat_1(X21)!=X20|X21=k1_wellord2(X20)|~v1_relat_1(X21))&(r2_hidden(k4_tarski(esk1_2(X20,X21),esk2_2(X20,X21)),X21)|r1_tarski(esk1_2(X20,X21),esk2_2(X20,X21))|k3_relat_1(X21)!=X20|X21=k1_wellord2(X20)|~v1_relat_1(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.20/0.38  fof(c_0_22, plain, ![X26]:v1_relat_1(k1_wellord2(X26)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.20/0.38  fof(c_0_23, plain, ![X14, X15]:(~v3_ordinal1(X14)|(~v3_ordinal1(X15)|(r2_xboole_0(X14,X15)|X14=X15|r2_xboole_0(X15,X14)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_ordinal1])])])])).
% 0.20/0.38  fof(c_0_24, plain, ![X18, X19]:(~v1_relat_1(X18)|(~v2_wellord1(X18)|(~r2_hidden(X19,k3_relat_1(X18))|~r4_wellord1(X18,k2_wellord1(X18,k1_wellord1(X18,X19)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.20/0.38  cnf(c_0_25, plain, (k1_wellord1(k1_wellord2(X1),X2)=X2|~r2_hidden(X2,X1)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_27, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_28, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_29, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_30, plain, (r2_xboole_0(X1,X2)|X1=X2|r2_xboole_0(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  fof(c_0_31, plain, ![X9]:((v1_ordinal1(X9)|~v3_ordinal1(X9))&(v2_ordinal1(X9)|~v3_ordinal1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.20/0.38  cnf(c_0_32, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (k1_wellord1(k1_wellord2(esk4_0),X1)=X1|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (v2_wellord1(k1_wellord2(esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.20/0.38  cnf(c_0_35, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_29])])).
% 0.20/0.38  fof(c_0_36, plain, ![X30, X31]:(~r1_tarski(X30,X31)|k2_wellord1(k1_wellord2(X31),X30)=k1_wellord2(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.20/0.38  fof(c_0_37, plain, ![X16, X17]:(~v1_relat_1(X16)|(~v1_relat_1(X17)|(~r4_wellord1(X16,X17)|r4_wellord1(X17,X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.20/0.38  fof(c_0_38, plain, ![X5, X6]:(((r1_tarski(X5,X6)|~r2_xboole_0(X5,X6))&(X5!=X6|~r2_xboole_0(X5,X6)))&(~r1_tarski(X5,X6)|X5=X6|r2_xboole_0(X5,X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (X1=esk4_0|r2_xboole_0(X1,esk4_0)|r2_xboole_0(esk4_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_42, plain, ![X10, X11]:(~v1_ordinal1(X10)|(~v3_ordinal1(X11)|(~r2_xboole_0(X10,X11)|r2_hidden(X10,X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).
% 0.20/0.38  cnf(c_0_43, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (~r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),X1))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_29]), c_0_35])])).
% 0.20/0.38  cnf(c_0_45, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_46, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (r2_xboole_0(esk4_0,esk3_0)|r2_xboole_0(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.20/0.38  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (v1_ordinal1(esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_40])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (~r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(X1))|~r2_hidden(X1,esk4_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_29]), c_0_29])])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r2_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r2_xboole_0(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_49]), c_0_51]), c_0_26])])).
% 0.20/0.38  fof(c_0_56, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (v1_ordinal1(esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_26])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)|~r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_54])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_55])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (k1_wellord1(k1_wellord2(esk3_0),X1)=X1|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_40])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (v2_wellord1(k1_wellord2(esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_40])).
% 0.20/0.38  cnf(c_0_63, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_54]), c_0_57]), c_0_40])])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (~r4_wellord1(k1_wellord2(esk3_0),k2_wellord1(k1_wellord2(esk3_0),X1))|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_61]), c_0_62]), c_0_29]), c_0_35])])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, (r4_wellord1(k1_wellord2(esk3_0),k2_wellord1(k1_wellord2(X1),esk4_0))|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_45])).
% 0.20/0.38  cnf(c_0_68, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_41]), c_0_65])])).
% 0.20/0.38  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_65])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 70
% 0.20/0.38  # Proof object clause steps            : 41
% 0.20/0.38  # Proof object formula steps           : 29
% 0.20/0.38  # Proof object conjectures             : 29
% 0.20/0.38  # Proof object clause conjectures      : 26
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 17
% 0.20/0.38  # Proof object initial formulas used   : 14
% 0.20/0.38  # Proof object generating inferences   : 22
% 0.20/0.38  # Proof object simplifying inferences  : 29
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 14
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 28
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 28
% 0.20/0.38  # Processed clauses                    : 101
% 0.20/0.38  # ...of these trivial                  : 2
% 0.20/0.38  # ...subsumed                          : 3
% 0.20/0.38  # ...remaining for further processing  : 96
% 0.20/0.38  # Other redundant clauses eliminated   : 10
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 4
% 0.20/0.38  # Generated clauses                    : 99
% 0.20/0.38  # ...of the previous two non-trivial   : 83
% 0.20/0.38  # Contextual simplify-reflections      : 2
% 0.20/0.38  # Paramodulations                      : 88
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 10
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 52
% 0.20/0.38  #    Positive orientable unit clauses  : 16
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 3
% 0.20/0.38  #    Non-unit-clauses                  : 33
% 0.20/0.38  # Current number of unprocessed clauses: 32
% 0.20/0.38  # ...number of literals in the above   : 113
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 34
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 214
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 99
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.20/0.38  # Unit Clause-clause subsumption calls : 63
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 5
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3615
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
