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
% DateTime   : Thu Dec  3 11:00:43 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 715 expanded)
%              Number of clauses        :   48 ( 278 expanded)
%              Number of leaves         :   14 ( 174 expanded)
%              Depth                    :   18
%              Number of atoms          :  230 (2390 expanded)
%              Number of equality atoms :   44 ( 435 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t57_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(t7_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v2_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(t10_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
           => X1 = k1_wellord1(k1_wellord2(X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(t8_wellord2,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(t40_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1))) = k1_wellord1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).

fof(t19_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord2])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ~ v3_ordinal1(X9)
      | ~ v3_ordinal1(X10)
      | r1_ordinal1(X9,X10)
      | r2_hidden(X10,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_16,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    & v3_ordinal1(esk4_0)
    & r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0))
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_17,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X7,X8] :
      ( ( ~ r1_ordinal1(X7,X8)
        | r1_tarski(X7,X8)
        | ~ v3_ordinal1(X7)
        | ~ v3_ordinal1(X8) )
      & ( ~ r1_tarski(X7,X8)
        | r1_ordinal1(X7,X8)
        | ~ v3_ordinal1(X7)
        | ~ v3_ordinal1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | r1_ordinal1(X1,esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X22,X23,X24,X25] :
      ( ( k3_relat_1(X23) = X22
        | X23 != k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X24,X25),X23)
        | r1_tarski(X24,X25)
        | ~ r2_hidden(X24,X22)
        | ~ r2_hidden(X25,X22)
        | X23 != k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r1_tarski(X24,X25)
        | r2_hidden(k4_tarski(X24,X25),X23)
        | ~ r2_hidden(X24,X22)
        | ~ r2_hidden(X25,X22)
        | X23 != k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk1_2(X22,X23),X22)
        | k3_relat_1(X23) != X22
        | X23 = k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk2_2(X22,X23),X22)
        | k3_relat_1(X23) != X22
        | X23 = k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X22,X23),esk2_2(X22,X23)),X23)
        | ~ r1_tarski(esk1_2(X22,X23),esk2_2(X22,X23))
        | k3_relat_1(X23) != X22
        | X23 = k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk1_2(X22,X23),esk2_2(X22,X23)),X23)
        | r1_tarski(esk1_2(X22,X23),esk2_2(X22,X23))
        | k3_relat_1(X23) != X22
        | X23 = k1_wellord2(X22)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_23,plain,(
    ! [X28] : v1_relat_1(k1_wellord2(X28)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_24,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | r1_ordinal1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | r1_ordinal1(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21])).

fof(c_0_28,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v2_wellord1(X20)
      | ~ r2_hidden(X21,k3_relat_1(X20))
      | ~ r4_wellord1(X20,k2_wellord1(X20,k1_wellord1(X20,X21))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

cnf(c_0_29,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_18]),c_0_21])])).

cnf(c_0_33,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_ordinal1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_18])).

fof(c_0_35,plain,(
    ! [X31] :
      ( ~ v3_ordinal1(X31)
      | v2_wellord1(k1_wellord2(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).

cnf(c_0_36,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ r1_tarski(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_tarski(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_34]),c_0_21]),c_0_18])])).

cnf(c_0_40,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X29,X30] :
      ( ~ v3_ordinal1(X29)
      | ~ v3_ordinal1(X30)
      | ~ r2_hidden(X29,X30)
      | X29 = k1_wellord1(k1_wellord2(X30),X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

cnf(c_0_42,plain,
    ( ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X2)))
    | ~ v2_wellord1(k1_wellord2(X1))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_30])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_18])).

cnf(c_0_45,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_46,plain,(
    ! [X32,X33] :
      ( ~ r1_tarski(X32,X33)
      | k2_wellord1(k1_wellord2(X33),X32) = k1_wellord2(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

fof(c_0_47,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | ~ r4_wellord1(X18,X19)
      | r4_wellord1(X19,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),k1_wellord1(k1_wellord2(esk4_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_49,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk4_0),esk3_0) = esk3_0
    | r2_hidden(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_18]),c_0_21])])).

cnf(c_0_50,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k2_wellord1(k1_wellord2(esk4_0),esk3_0) = k1_wellord2(esk3_0)
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_32])).

cnf(c_0_55,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_30]),c_0_30])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

fof(c_0_57,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ v2_wellord1(X17)
      | k3_relat_1(k2_wellord1(X17,k1_wellord1(X17,X16))) = k1_wellord1(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_wellord1])])).

cnf(c_0_58,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk3_0),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_56]),c_0_21]),c_0_18])])).

cnf(c_0_60,plain,
    ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2))) = k1_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk3_0),k2_wellord1(k1_wellord2(esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_56]),c_0_58])]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( k2_wellord1(k1_wellord2(esk3_0),esk4_0) = k1_wellord2(esk4_0)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_39])).

cnf(c_0_63,plain,
    ( k3_relat_1(k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X2))) = k1_wellord1(k1_wellord2(X1),X2)
    | ~ v2_wellord1(k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_52])])).

fof(c_0_65,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(X13,k3_relat_1(X15))
        | ~ r2_hidden(X13,k3_relat_1(k2_wellord1(X15,X14)))
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(X13,X14)
        | ~ r2_hidden(X13,k3_relat_1(k2_wellord1(X15,X14)))
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).

cnf(c_0_66,negated_conjecture,
    ( k3_relat_1(k2_wellord1(k1_wellord2(esk4_0),k1_wellord1(k1_wellord2(esk4_0),X1))) = k1_wellord1(k1_wellord2(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_44])).

cnf(c_0_67,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk4_0),esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_64]),c_0_18]),c_0_21])])).

fof(c_0_68,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | ~ r1_tarski(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k3_relat_1(k2_wellord1(k1_wellord2(esk4_0),esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_37]),c_0_30])])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_56]),c_0_75]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.20/0.38  # and selection function SelectGrCQArEqFirst.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t11_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 0.20/0.38  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.20/0.38  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.20/0.38  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.20/0.38  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 0.20/0.38  fof(t7_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 0.20/0.38  fof(t10_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>X1=k1_wellord1(k1_wellord2(X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 0.20/0.38  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 0.20/0.38  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 0.20/0.38  fof(t40_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v2_wellord1(X2)=>k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1)))=k1_wellord1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_wellord1)).
% 0.20/0.38  fof(t19_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_wellord1)).
% 0.20/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.38  fof(c_0_14, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2)))), inference(assume_negation,[status(cth)],[t11_wellord2])).
% 0.20/0.38  fof(c_0_15, plain, ![X9, X10]:(~v3_ordinal1(X9)|(~v3_ordinal1(X10)|(r1_ordinal1(X9,X10)|r2_hidden(X10,X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.20/0.38  fof(c_0_16, negated_conjecture, (v3_ordinal1(esk3_0)&(v3_ordinal1(esk4_0)&(r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0))&esk3_0!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.38  cnf(c_0_17, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  fof(c_0_19, plain, ![X7, X8]:((~r1_ordinal1(X7,X8)|r1_tarski(X7,X8)|(~v3_ordinal1(X7)|~v3_ordinal1(X8)))&(~r1_tarski(X7,X8)|r1_ordinal1(X7,X8)|(~v3_ordinal1(X7)|~v3_ordinal1(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(esk4_0,X1)|r1_ordinal1(X1,esk4_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  fof(c_0_22, plain, ![X22, X23, X24, X25]:(((k3_relat_1(X23)=X22|X23!=k1_wellord2(X22)|~v1_relat_1(X23))&((~r2_hidden(k4_tarski(X24,X25),X23)|r1_tarski(X24,X25)|(~r2_hidden(X24,X22)|~r2_hidden(X25,X22))|X23!=k1_wellord2(X22)|~v1_relat_1(X23))&(~r1_tarski(X24,X25)|r2_hidden(k4_tarski(X24,X25),X23)|(~r2_hidden(X24,X22)|~r2_hidden(X25,X22))|X23!=k1_wellord2(X22)|~v1_relat_1(X23))))&(((r2_hidden(esk1_2(X22,X23),X22)|k3_relat_1(X23)!=X22|X23=k1_wellord2(X22)|~v1_relat_1(X23))&(r2_hidden(esk2_2(X22,X23),X22)|k3_relat_1(X23)!=X22|X23=k1_wellord2(X22)|~v1_relat_1(X23)))&((~r2_hidden(k4_tarski(esk1_2(X22,X23),esk2_2(X22,X23)),X23)|~r1_tarski(esk1_2(X22,X23),esk2_2(X22,X23))|k3_relat_1(X23)!=X22|X23=k1_wellord2(X22)|~v1_relat_1(X23))&(r2_hidden(k4_tarski(esk1_2(X22,X23),esk2_2(X22,X23)),X23)|r1_tarski(esk1_2(X22,X23),esk2_2(X22,X23))|k3_relat_1(X23)!=X22|X23=k1_wellord2(X22)|~v1_relat_1(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.20/0.38  fof(c_0_23, plain, ![X28]:v1_relat_1(k1_wellord2(X28)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.20/0.38  fof(c_0_24, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|r1_ordinal1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(esk3_0,X1)|r1_ordinal1(X1,esk3_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_21])).
% 0.20/0.38  fof(c_0_28, plain, ![X20, X21]:(~v1_relat_1(X20)|(~v2_wellord1(X20)|(~r2_hidden(X21,k3_relat_1(X20))|~r4_wellord1(X20,k2_wellord1(X20,k1_wellord1(X20,X21)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.20/0.38  cnf(c_0_29, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_30, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_31, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_18]), c_0_21])])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_ordinal1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_18])).
% 0.20/0.38  fof(c_0_35, plain, ![X31]:(~v3_ordinal1(X31)|v2_wellord1(k1_wellord2(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).
% 0.20/0.38  cnf(c_0_36, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_37, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_29]), c_0_30])])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|~r1_tarski(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_tarski(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_34]), c_0_21]), c_0_18])])).
% 0.20/0.38  cnf(c_0_40, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  fof(c_0_41, plain, ![X29, X30]:(~v3_ordinal1(X29)|(~v3_ordinal1(X30)|(~r2_hidden(X29,X30)|X29=k1_wellord1(k1_wellord2(X30),X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).
% 0.20/0.38  cnf(c_0_42, plain, (~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X2)))|~v2_wellord1(k1_wellord2(X1))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_30])])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (v2_wellord1(k1_wellord2(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_18])).
% 0.20/0.38  cnf(c_0_45, plain, (X1=k1_wellord1(k1_wellord2(X2),X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.38  fof(c_0_46, plain, ![X32, X33]:(~r1_tarski(X32,X33)|k2_wellord1(k1_wellord2(X33),X32)=k1_wellord2(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.20/0.38  fof(c_0_47, plain, ![X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|(~r4_wellord1(X18,X19)|r4_wellord1(X19,X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|~r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),k1_wellord1(k1_wellord2(esk4_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (k1_wellord1(k1_wellord2(esk4_0),esk3_0)=esk3_0|r2_hidden(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_43]), c_0_18]), c_0_21])])).
% 0.20/0.38  cnf(c_0_50, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.38  cnf(c_0_51, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|~r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk3_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (k2_wellord1(k1_wellord2(esk4_0),esk3_0)=k1_wellord2(esk3_0)|r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_32])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_30]), c_0_30])])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.20/0.38  fof(c_0_57, plain, ![X16, X17]:(~v1_relat_1(X17)|(~v2_wellord1(X17)|k3_relat_1(k2_wellord1(X17,k1_wellord1(X17,X16)))=k1_wellord1(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_wellord1])])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (v2_wellord1(k1_wellord2(esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_21])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (k1_wellord1(k1_wellord2(esk3_0),esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_56]), c_0_21]), c_0_18])])).
% 0.20/0.38  cnf(c_0_60, plain, (k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2)))=k1_wellord1(X1,X2)|~v1_relat_1(X1)|~v2_wellord1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (~r4_wellord1(k1_wellord2(esk3_0),k2_wellord1(k1_wellord2(esk3_0),esk4_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_56]), c_0_58])]), c_0_59])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (k2_wellord1(k1_wellord2(esk3_0),esk4_0)=k1_wellord2(esk4_0)|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_39])).
% 0.20/0.38  cnf(c_0_63, plain, (k3_relat_1(k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X2)))=k1_wellord1(k1_wellord2(X1),X2)|~v2_wellord1(k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_60, c_0_30])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_52])])).
% 0.20/0.38  fof(c_0_65, plain, ![X13, X14, X15]:((r2_hidden(X13,k3_relat_1(X15))|~r2_hidden(X13,k3_relat_1(k2_wellord1(X15,X14)))|~v1_relat_1(X15))&(r2_hidden(X13,X14)|~r2_hidden(X13,k3_relat_1(k2_wellord1(X15,X14)))|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (k3_relat_1(k2_wellord1(k1_wellord2(esk4_0),k1_wellord1(k1_wellord2(esk4_0),X1)))=k1_wellord1(k1_wellord2(esk4_0),X1)), inference(spm,[status(thm)],[c_0_63, c_0_44])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, (k1_wellord1(k1_wellord2(esk4_0),esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_64]), c_0_18]), c_0_21])])).
% 0.20/0.38  fof(c_0_68, plain, ![X11, X12]:(~r2_hidden(X11,X12)|~r1_tarski(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.38  cnf(c_0_69, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_70, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, (k3_relat_1(k2_wellord1(k1_wellord2(esk4_0),esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.38  cnf(c_0_72, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.38  cnf(c_0_73, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_69])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_37]), c_0_30])])).
% 0.20/0.38  cnf(c_0_75, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.38  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_56]), c_0_75]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 77
% 0.20/0.38  # Proof object clause steps            : 48
% 0.20/0.38  # Proof object formula steps           : 29
% 0.20/0.38  # Proof object conjectures             : 32
% 0.20/0.38  # Proof object clause conjectures      : 29
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 18
% 0.20/0.38  # Proof object initial formulas used   : 14
% 0.20/0.38  # Proof object generating inferences   : 28
% 0.20/0.38  # Proof object simplifying inferences  : 38
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 14
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 27
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 27
% 0.20/0.38  # Processed clauses                    : 107
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 3
% 0.20/0.38  # ...remaining for further processing  : 104
% 0.20/0.38  # Other redundant clauses eliminated   : 9
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 12
% 0.20/0.38  # Generated clauses                    : 93
% 0.20/0.38  # ...of the previous two non-trivial   : 73
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 84
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 9
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
% 0.20/0.38  # Current number of processed clauses  : 57
% 0.20/0.38  #    Positive orientable unit clauses  : 21
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 4
% 0.20/0.38  #    Non-unit-clauses                  : 32
% 0.20/0.38  # Current number of unprocessed clauses: 13
% 0.20/0.38  # ...number of literals in the above   : 35
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 38
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 298
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 190
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.20/0.38  # Unit Clause-clause subsumption calls : 113
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 6
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3833
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
