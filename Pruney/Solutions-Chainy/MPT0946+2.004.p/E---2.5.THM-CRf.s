%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:42 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 652 expanded)
%              Number of clauses        :   56 ( 261 expanded)
%              Number of leaves         :   14 ( 167 expanded)
%              Depth                    :   13
%              Number of atoms          :  274 (2204 expanded)
%              Number of equality atoms :   42 ( 467 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(t10_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
           => X1 = k1_wellord1(k1_wellord2(X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(t7_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v2_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

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

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(t57_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(t8_wellord2,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t52_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X2,X3) )
               => r4_wellord1(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).

fof(t19_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord2])).

fof(c_0_15,plain,(
    ! [X30,X31] :
      ( ~ v3_ordinal1(X30)
      | ~ v3_ordinal1(X31)
      | ~ r2_hidden(X30,X31)
      | X30 = k1_wellord1(k1_wellord2(X31),X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

fof(c_0_16,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    & v3_ordinal1(esk4_0)
    & r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0))
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ~ v3_ordinal1(X7)
      | ~ v3_ordinal1(X8)
      | r1_ordinal1(X7,X8)
      | r1_ordinal1(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

cnf(c_0_18,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X32] :
      ( ~ v3_ordinal1(X32)
      | v2_wellord1(k1_wellord2(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).

fof(c_0_21,plain,(
    ! [X23,X24,X25,X26] :
      ( ( k3_relat_1(X24) = X23
        | X24 != k1_wellord2(X23)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X25,X26),X24)
        | r1_tarski(X25,X26)
        | ~ r2_hidden(X25,X23)
        | ~ r2_hidden(X26,X23)
        | X24 != k1_wellord2(X23)
        | ~ v1_relat_1(X24) )
      & ( ~ r1_tarski(X25,X26)
        | r2_hidden(k4_tarski(X25,X26),X24)
        | ~ r2_hidden(X25,X23)
        | ~ r2_hidden(X26,X23)
        | X24 != k1_wellord2(X23)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk1_2(X23,X24),X23)
        | k3_relat_1(X24) != X23
        | X24 = k1_wellord2(X23)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk2_2(X23,X24),X23)
        | k3_relat_1(X24) != X23
        | X24 = k1_wellord2(X23)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X23,X24),esk2_2(X23,X24)),X24)
        | ~ r1_tarski(esk1_2(X23,X24),esk2_2(X23,X24))
        | k3_relat_1(X24) != X23
        | X24 = k1_wellord2(X23)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk1_2(X23,X24),esk2_2(X23,X24)),X24)
        | r1_tarski(esk1_2(X23,X24),esk2_2(X23,X24))
        | k3_relat_1(X24) != X23
        | X24 = k1_wellord2(X23)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_22,plain,(
    ! [X29] : v1_relat_1(k1_wellord2(X29)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_23,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | ~ r4_wellord1(X16,X17)
      | r4_wellord1(X17,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_24,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v2_wellord1(X21)
      | ~ r2_hidden(X22,k3_relat_1(X21))
      | ~ r4_wellord1(X21,k2_wellord1(X21,k1_wellord1(X21,X22))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

cnf(c_0_26,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk4_0),X1) = X1
    | ~ r2_hidden(X1,esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_33,plain,(
    ! [X33,X34] :
      ( ~ r1_tarski(X33,X34)
      | k2_wellord1(k1_wellord2(X34),X33) = k1_wellord2(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

fof(c_0_34,plain,(
    ! [X9,X10] :
      ( ( ~ r1_ordinal1(X9,X10)
        | r1_tarski(X9,X10)
        | ~ v3_ordinal1(X9)
        | ~ v3_ordinal1(X10) )
      & ( ~ r1_tarski(X9,X10)
        | r1_ordinal1(X9,X10)
        | ~ v3_ordinal1(X9)
        | ~ v3_ordinal1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_35,negated_conjecture,
    ( r1_ordinal1(X1,esk4_0)
    | r1_ordinal1(esk4_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_36,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk4_0),esk3_0) = esk3_0
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19])).

cnf(c_0_39,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_30])])).

cnf(c_0_40,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_30]),c_0_30])])).

cnf(c_0_41,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk3_0)
    | r1_ordinal1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

fof(c_0_44,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | ~ r4_wellord1(X18,X19)
      | ~ r4_wellord1(X19,X20)
      | r4_wellord1(X18,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_wellord1])])])).

fof(c_0_45,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(X13,k3_relat_1(X15))
        | ~ r2_hidden(X13,k3_relat_1(k2_wellord1(X15,X14)))
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(X13,X14)
        | ~ r2_hidden(X13,k3_relat_1(k2_wellord1(X15,X14)))
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).

cnf(c_0_46,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk3_0))
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_30]),c_0_39])])).

cnf(c_0_47,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(X1),esk3_0))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk3_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_19]),c_0_27])])).

fof(c_0_49,plain,(
    ! [X11,X12] :
      ( ~ v3_ordinal1(X11)
      | ~ v3_ordinal1(X12)
      | r2_hidden(X11,X12)
      | X11 = X12
      | r2_hidden(X12,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_50,plain,
    ( r4_wellord1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r4_wellord1(X1,X2)
    | ~ r4_wellord1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0)
    | ~ r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_48]),c_0_27]),c_0_19])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk3_0),X1) = X1
    | ~ r2_hidden(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( r4_wellord1(X1,k1_wellord2(esk3_0))
    | ~ r4_wellord1(X1,k1_wellord2(esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_40]),c_0_30]),c_0_30])])).

fof(c_0_57,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_41]),c_0_39]),c_0_30]),c_0_39])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( X1 = esk4_0
    | r2_hidden(X1,esk4_0)
    | r2_hidden(esk4_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_62,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk3_0),esk3_0) = esk3_0
    | ~ r2_hidden(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_27])).

cnf(c_0_63,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_64,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk3_0),X1)
    | ~ r4_wellord1(X1,k1_wellord2(esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_56]),c_0_30])])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk3_0),esk4_0) = esk4_0
    | ~ r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_19])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_27]),c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk3_0),k2_wellord1(k1_wellord2(esk3_0),esk3_0))
    | ~ r2_hidden(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_62]),c_0_63]),c_0_30]),c_0_39])])).

cnf(c_0_70,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_32]),c_0_30])])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk4_0),esk4_0) = esk4_0
    | ~ r2_hidden(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_73,negated_conjecture,
    ( r4_wellord1(X1,k1_wellord2(esk4_0))
    | ~ r4_wellord1(X1,k1_wellord2(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_32]),c_0_30]),c_0_30])])).

cnf(c_0_74,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk3_0),k2_wellord1(k1_wellord2(esk3_0),esk4_0))
    | ~ r2_hidden(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_66]),c_0_63]),c_0_30]),c_0_39])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_41]),c_0_70]),c_0_71])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk4_0))
    | ~ r2_hidden(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_72]),c_0_38]),c_0_30]),c_0_39])])).

cnf(c_0_78,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_40]),c_0_30])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0)
    | ~ r1_tarski(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_41]),c_0_32])])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_68]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | r1_tarski(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_53])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_41]),c_0_78]),c_0_71])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_80]),c_0_82]),c_0_83]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:27:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.15/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.030 s
% 0.15/0.39  # Presaturation interreduction done
% 0.15/0.39  
% 0.15/0.39  # Proof found!
% 0.15/0.39  # SZS status Theorem
% 0.15/0.39  # SZS output start CNFRefutation
% 0.15/0.39  fof(t11_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 0.15/0.39  fof(t10_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>X1=k1_wellord1(k1_wellord2(X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 0.15/0.39  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 0.15/0.39  fof(t7_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 0.15/0.39  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.15/0.39  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.15/0.39  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 0.15/0.39  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 0.15/0.39  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 0.15/0.39  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.15/0.39  fof(t52_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>((r4_wellord1(X1,X2)&r4_wellord1(X2,X3))=>r4_wellord1(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_wellord1)).
% 0.15/0.39  fof(t19_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_wellord1)).
% 0.15/0.39  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.15/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.15/0.40  fof(c_0_14, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2)))), inference(assume_negation,[status(cth)],[t11_wellord2])).
% 0.15/0.40  fof(c_0_15, plain, ![X30, X31]:(~v3_ordinal1(X30)|(~v3_ordinal1(X31)|(~r2_hidden(X30,X31)|X30=k1_wellord1(k1_wellord2(X31),X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).
% 0.15/0.40  fof(c_0_16, negated_conjecture, (v3_ordinal1(esk3_0)&(v3_ordinal1(esk4_0)&(r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0))&esk3_0!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.15/0.40  fof(c_0_17, plain, ![X7, X8]:(~v3_ordinal1(X7)|~v3_ordinal1(X8)|(r1_ordinal1(X7,X8)|r1_ordinal1(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 0.15/0.40  cnf(c_0_18, plain, (X1=k1_wellord1(k1_wellord2(X2),X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.40  cnf(c_0_19, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.40  fof(c_0_20, plain, ![X32]:(~v3_ordinal1(X32)|v2_wellord1(k1_wellord2(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).
% 0.15/0.40  fof(c_0_21, plain, ![X23, X24, X25, X26]:(((k3_relat_1(X24)=X23|X24!=k1_wellord2(X23)|~v1_relat_1(X24))&((~r2_hidden(k4_tarski(X25,X26),X24)|r1_tarski(X25,X26)|(~r2_hidden(X25,X23)|~r2_hidden(X26,X23))|X24!=k1_wellord2(X23)|~v1_relat_1(X24))&(~r1_tarski(X25,X26)|r2_hidden(k4_tarski(X25,X26),X24)|(~r2_hidden(X25,X23)|~r2_hidden(X26,X23))|X24!=k1_wellord2(X23)|~v1_relat_1(X24))))&(((r2_hidden(esk1_2(X23,X24),X23)|k3_relat_1(X24)!=X23|X24=k1_wellord2(X23)|~v1_relat_1(X24))&(r2_hidden(esk2_2(X23,X24),X23)|k3_relat_1(X24)!=X23|X24=k1_wellord2(X23)|~v1_relat_1(X24)))&((~r2_hidden(k4_tarski(esk1_2(X23,X24),esk2_2(X23,X24)),X24)|~r1_tarski(esk1_2(X23,X24),esk2_2(X23,X24))|k3_relat_1(X24)!=X23|X24=k1_wellord2(X23)|~v1_relat_1(X24))&(r2_hidden(k4_tarski(esk1_2(X23,X24),esk2_2(X23,X24)),X24)|r1_tarski(esk1_2(X23,X24),esk2_2(X23,X24))|k3_relat_1(X24)!=X23|X24=k1_wellord2(X23)|~v1_relat_1(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.15/0.40  fof(c_0_22, plain, ![X29]:v1_relat_1(k1_wellord2(X29)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.15/0.40  fof(c_0_23, plain, ![X16, X17]:(~v1_relat_1(X16)|(~v1_relat_1(X17)|(~r4_wellord1(X16,X17)|r4_wellord1(X17,X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.15/0.40  cnf(c_0_24, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.40  fof(c_0_25, plain, ![X21, X22]:(~v1_relat_1(X21)|(~v2_wellord1(X21)|(~r2_hidden(X22,k3_relat_1(X21))|~r4_wellord1(X21,k2_wellord1(X21,k1_wellord1(X21,X22)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.15/0.40  cnf(c_0_26, negated_conjecture, (k1_wellord1(k1_wellord2(esk4_0),X1)=X1|~r2_hidden(X1,esk4_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.15/0.40  cnf(c_0_27, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.40  cnf(c_0_28, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.40  cnf(c_0_29, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.40  cnf(c_0_30, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.40  cnf(c_0_31, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.15/0.40  cnf(c_0_32, negated_conjecture, (r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.40  fof(c_0_33, plain, ![X33, X34]:(~r1_tarski(X33,X34)|k2_wellord1(k1_wellord2(X34),X33)=k1_wellord2(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.15/0.40  fof(c_0_34, plain, ![X9, X10]:((~r1_ordinal1(X9,X10)|r1_tarski(X9,X10)|(~v3_ordinal1(X9)|~v3_ordinal1(X10)))&(~r1_tarski(X9,X10)|r1_ordinal1(X9,X10)|(~v3_ordinal1(X9)|~v3_ordinal1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.15/0.40  cnf(c_0_35, negated_conjecture, (r1_ordinal1(X1,esk4_0)|r1_ordinal1(esk4_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_19])).
% 0.15/0.40  cnf(c_0_36, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.40  cnf(c_0_37, negated_conjecture, (k1_wellord1(k1_wellord2(esk4_0),esk3_0)=esk3_0|~r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.15/0.40  cnf(c_0_38, negated_conjecture, (v2_wellord1(k1_wellord2(esk4_0))), inference(spm,[status(thm)],[c_0_28, c_0_19])).
% 0.15/0.40  cnf(c_0_39, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_29]), c_0_30])])).
% 0.15/0.40  cnf(c_0_40, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_30]), c_0_30])])).
% 0.15/0.40  cnf(c_0_41, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.15/0.40  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.15/0.40  cnf(c_0_43, negated_conjecture, (r1_ordinal1(esk4_0,esk3_0)|r1_ordinal1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_27])).
% 0.15/0.40  fof(c_0_44, plain, ![X18, X19, X20]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|(~v1_relat_1(X20)|(~r4_wellord1(X18,X19)|~r4_wellord1(X19,X20)|r4_wellord1(X18,X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_wellord1])])])).
% 0.15/0.40  fof(c_0_45, plain, ![X13, X14, X15]:((r2_hidden(X13,k3_relat_1(X15))|~r2_hidden(X13,k3_relat_1(k2_wellord1(X15,X14)))|~v1_relat_1(X15))&(r2_hidden(X13,X14)|~r2_hidden(X13,k3_relat_1(k2_wellord1(X15,X14)))|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).
% 0.15/0.40  cnf(c_0_46, negated_conjecture, (~r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk3_0))|~r2_hidden(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_30]), c_0_39])])).
% 0.15/0.40  cnf(c_0_47, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(X1),esk3_0))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.15/0.40  cnf(c_0_48, negated_conjecture, (r1_ordinal1(esk4_0,esk3_0)|r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_19]), c_0_27])])).
% 0.15/0.40  fof(c_0_49, plain, ![X11, X12]:(~v3_ordinal1(X11)|(~v3_ordinal1(X12)|(r2_hidden(X11,X12)|X11=X12|r2_hidden(X12,X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.15/0.40  cnf(c_0_50, plain, (r4_wellord1(X1,X3)|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r4_wellord1(X1,X2)|~r4_wellord1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.15/0.40  cnf(c_0_51, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.15/0.40  cnf(c_0_52, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)|~r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.15/0.40  cnf(c_0_53, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_48]), c_0_27]), c_0_19])])).
% 0.15/0.40  cnf(c_0_54, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.15/0.40  cnf(c_0_55, negated_conjecture, (k1_wellord1(k1_wellord2(esk3_0),X1)=X1|~r2_hidden(X1,esk3_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_27])).
% 0.15/0.40  cnf(c_0_56, negated_conjecture, (r4_wellord1(X1,k1_wellord2(esk3_0))|~r4_wellord1(X1,k1_wellord2(esk4_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_40]), c_0_30]), c_0_30])])).
% 0.15/0.40  fof(c_0_57, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.15/0.40  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_41]), c_0_39]), c_0_30]), c_0_39])])).
% 0.15/0.40  cnf(c_0_59, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.15/0.40  cnf(c_0_60, negated_conjecture, (X1=esk4_0|r2_hidden(X1,esk4_0)|r2_hidden(esk4_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_19])).
% 0.15/0.40  cnf(c_0_61, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.40  cnf(c_0_62, negated_conjecture, (k1_wellord1(k1_wellord2(esk3_0),esk3_0)=esk3_0|~r2_hidden(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_27])).
% 0.15/0.40  cnf(c_0_63, negated_conjecture, (v2_wellord1(k1_wellord2(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.15/0.40  cnf(c_0_64, negated_conjecture, (r4_wellord1(k1_wellord2(esk3_0),X1)|~r4_wellord1(X1,k1_wellord2(esk4_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_56]), c_0_30])])).
% 0.15/0.40  cnf(c_0_65, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.15/0.40  cnf(c_0_66, negated_conjecture, (k1_wellord1(k1_wellord2(esk3_0),esk4_0)=esk4_0|~r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_19])).
% 0.15/0.40  cnf(c_0_67, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(esk3_0,esk4_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.15/0.40  cnf(c_0_68, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_27]), c_0_61])).
% 0.15/0.40  cnf(c_0_69, negated_conjecture, (~r4_wellord1(k1_wellord2(esk3_0),k2_wellord1(k1_wellord2(esk3_0),esk3_0))|~r2_hidden(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_62]), c_0_63]), c_0_30]), c_0_39])])).
% 0.15/0.40  cnf(c_0_70, negated_conjecture, (r4_wellord1(k1_wellord2(esk3_0),k1_wellord2(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_32]), c_0_30])])).
% 0.15/0.40  cnf(c_0_71, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_65])).
% 0.15/0.40  cnf(c_0_72, negated_conjecture, (k1_wellord1(k1_wellord2(esk4_0),esk4_0)=esk4_0|~r2_hidden(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_19])).
% 0.15/0.40  cnf(c_0_73, negated_conjecture, (r4_wellord1(X1,k1_wellord2(esk4_0))|~r4_wellord1(X1,k1_wellord2(esk3_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_32]), c_0_30]), c_0_30])])).
% 0.15/0.40  cnf(c_0_74, negated_conjecture, (~r4_wellord1(k1_wellord2(esk3_0),k2_wellord1(k1_wellord2(esk3_0),esk4_0))|~r2_hidden(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_66]), c_0_63]), c_0_30]), c_0_39])])).
% 0.15/0.40  cnf(c_0_75, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.15/0.40  cnf(c_0_76, negated_conjecture, (~r2_hidden(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_41]), c_0_70]), c_0_71])])).
% 0.15/0.40  cnf(c_0_77, negated_conjecture, (~r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk4_0))|~r2_hidden(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_72]), c_0_38]), c_0_30]), c_0_39])])).
% 0.15/0.40  cnf(c_0_78, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_40]), c_0_30])])).
% 0.15/0.40  cnf(c_0_79, negated_conjecture, (~r2_hidden(esk4_0,esk3_0)|~r1_tarski(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_41]), c_0_32])])).
% 0.15/0.40  cnf(c_0_80, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_68]), c_0_76])).
% 0.15/0.40  cnf(c_0_81, negated_conjecture, (r2_hidden(X1,esk4_0)|r1_tarski(esk4_0,esk3_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_58, c_0_53])).
% 0.15/0.40  cnf(c_0_82, negated_conjecture, (~r2_hidden(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_41]), c_0_78]), c_0_71])])).
% 0.15/0.40  cnf(c_0_83, negated_conjecture, (~r1_tarski(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 0.15/0.40  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_80]), c_0_82]), c_0_83]), ['proof']).
% 0.15/0.40  # SZS output end CNFRefutation
% 0.15/0.40  # Proof object total steps             : 85
% 0.15/0.40  # Proof object clause steps            : 56
% 0.15/0.40  # Proof object formula steps           : 29
% 0.15/0.40  # Proof object conjectures             : 43
% 0.15/0.40  # Proof object clause conjectures      : 40
% 0.15/0.40  # Proof object formula conjectures     : 3
% 0.15/0.40  # Proof object initial clauses used    : 17
% 0.15/0.40  # Proof object initial formulas used   : 14
% 0.15/0.40  # Proof object generating inferences   : 36
% 0.15/0.40  # Proof object simplifying inferences  : 59
% 0.15/0.40  # Training examples: 0 positive, 0 negative
% 0.15/0.40  # Parsed axioms                        : 14
% 0.15/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.40  # Initial clauses                      : 27
% 0.15/0.40  # Removed in clause preprocessing      : 0
% 0.15/0.40  # Initial clauses in saturation        : 27
% 0.15/0.40  # Processed clauses                    : 127
% 0.15/0.40  # ...of these trivial                  : 1
% 0.15/0.40  # ...subsumed                          : 9
% 0.15/0.40  # ...remaining for further processing  : 116
% 0.15/0.40  # Other redundant clauses eliminated   : 9
% 0.15/0.40  # Clauses deleted for lack of memory   : 0
% 0.15/0.40  # Backward-subsumed                    : 0
% 0.15/0.40  # Backward-rewritten                   : 6
% 0.15/0.40  # Generated clauses                    : 244
% 0.15/0.40  # ...of the previous two non-trivial   : 216
% 0.15/0.40  # Contextual simplify-reflections      : 0
% 0.15/0.40  # Paramodulations                      : 234
% 0.15/0.40  # Factorizations                       : 0
% 0.15/0.40  # Equation resolutions                 : 9
% 0.15/0.40  # Propositional unsat checks           : 0
% 0.15/0.40  #    Propositional check models        : 0
% 0.15/0.40  #    Propositional check unsatisfiable : 0
% 0.15/0.40  #    Propositional clauses             : 0
% 0.15/0.40  #    Propositional clauses after purity: 0
% 0.15/0.40  #    Propositional unsat core size     : 0
% 0.15/0.40  #    Propositional preprocessing time  : 0.000
% 0.15/0.40  #    Propositional encoding time       : 0.000
% 0.15/0.40  #    Propositional solver time         : 0.000
% 0.15/0.40  #    Success case prop preproc time    : 0.000
% 0.15/0.40  #    Success case prop encoding time   : 0.000
% 0.15/0.40  #    Success case prop solver time     : 0.000
% 0.15/0.40  # Current number of processed clauses  : 74
% 0.15/0.40  #    Positive orientable unit clauses  : 14
% 0.15/0.40  #    Positive unorientable unit clauses: 0
% 0.15/0.40  #    Negative unit clauses             : 5
% 0.15/0.40  #    Non-unit-clauses                  : 55
% 0.15/0.40  # Current number of unprocessed clauses: 142
% 0.15/0.40  # ...number of literals in the above   : 516
% 0.15/0.40  # Current number of archived formulas  : 0
% 0.15/0.40  # Current number of archived clauses   : 33
% 0.15/0.40  # Clause-clause subsumption calls (NU) : 291
% 0.15/0.40  # Rec. Clause-clause subsumption calls : 221
% 0.15/0.40  # Non-unit clause-clause subsumptions  : 4
% 0.15/0.40  # Unit Clause-clause subsumption calls : 111
% 0.15/0.40  # Rewrite failures with RHS unbound    : 0
% 0.15/0.40  # BW rewrite match attempts            : 3
% 0.15/0.40  # BW rewrite match successes           : 1
% 0.15/0.40  # Condensation attempts                : 0
% 0.15/0.40  # Condensation successes               : 0
% 0.15/0.40  # Termbank termtop insertions          : 5958
% 0.15/0.40  
% 0.15/0.40  # -------------------------------------------------
% 0.15/0.40  # User time                : 0.044 s
% 0.15/0.40  # System time              : 0.004 s
% 0.15/0.40  # Total time               : 0.047 s
% 0.15/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
