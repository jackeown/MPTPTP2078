%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:45 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 566 expanded)
%              Number of clauses        :   43 ( 229 expanded)
%              Number of leaves         :   12 ( 141 expanded)
%              Depth                    :   19
%              Number of atoms          :  207 (1879 expanded)
%              Number of equality atoms :   43 ( 418 expanded)
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

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(t40_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1))) = k1_wellord1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

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

fof(t19_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(t57_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord2])).

fof(c_0_13,plain,(
    ! [X11,X12] :
      ( ~ v3_ordinal1(X11)
      | ~ v3_ordinal1(X12)
      | r2_hidden(X11,X12)
      | X11 = X12
      | r2_hidden(X12,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_14,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & v3_ordinal1(esk5_0)
    & r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ v2_wellord1(X17)
      | k3_relat_1(k2_wellord1(X17,k1_wellord1(X17,X16))) = k1_wellord1(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_wellord1])])).

fof(c_0_16,plain,(
    ! [X28] : v1_relat_1(k1_wellord2(X28)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_17,plain,(
    ! [X31] :
      ( ~ v3_ordinal1(X31)
      | v2_wellord1(k1_wellord2(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2))) = k1_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X29,X30] :
      ( ~ v3_ordinal1(X29)
      | ~ v3_ordinal1(X30)
      | ~ r2_hidden(X29,X30)
      | X29 = k1_wellord1(k1_wellord2(X30),X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

cnf(c_0_24,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(X1,esk5_0)
    | r2_hidden(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( k3_relat_1(k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X2))) = k1_wellord1(k1_wellord2(X1),X2)
    | ~ v2_wellord1(k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_29,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

fof(c_0_31,plain,(
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
      & ( r2_hidden(esk2_2(X22,X23),X22)
        | k3_relat_1(X23) != X22
        | X23 = k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk3_2(X22,X23),X22)
        | k3_relat_1(X23) != X22
        | X23 = k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X22,X23),esk3_2(X22,X23)),X23)
        | ~ r1_tarski(esk2_2(X22,X23),esk3_2(X22,X23))
        | k3_relat_1(X23) != X22
        | X23 = k1_wellord2(X22)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk2_2(X22,X23),esk3_2(X22,X23)),X23)
        | r1_tarski(esk2_2(X22,X23),esk3_2(X22,X23))
        | k3_relat_1(X23) != X22
        | X23 = k1_wellord2(X22)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_32,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(X13,k3_relat_1(X15))
        | ~ r2_hidden(X13,k3_relat_1(k2_wellord1(X15,X14)))
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(X13,X14)
        | ~ r2_hidden(X13,k3_relat_1(k2_wellord1(X15,X14)))
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).

cnf(c_0_33,negated_conjecture,
    ( k3_relat_1(k2_wellord1(k1_wellord2(esk5_0),k1_wellord1(k1_wellord2(esk5_0),X1))) = k1_wellord1(k1_wellord2(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk5_0),esk4_0) = esk4_0
    | r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_19]),c_0_25])])).

cnf(c_0_35,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v2_wellord1(X20)
      | ~ r2_hidden(X21,k3_relat_1(X20))
      | ~ r4_wellord1(X20,k2_wellord1(X20,k1_wellord1(X20,X21))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k3_relat_1(k2_wellord1(k1_wellord2(esk5_0),esk4_0)) = esk4_0
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_21])])).

fof(c_0_40,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_41,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_21])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,plain,
    ( ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X2)))
    | ~ v2_wellord1(k1_wellord2(X1))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_21])])).

fof(c_0_45,plain,(
    ! [X32,X33] :
      ( ~ r1_tarski(X32,X33)
      | k2_wellord1(k1_wellord2(X33),X32) = k1_wellord2(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk5_0)
    | r2_hidden(esk5_0,esk4_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_48,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | ~ r4_wellord1(X18,X19)
      | r4_wellord1(X19,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ r4_wellord1(k1_wellord2(esk5_0),k2_wellord1(k1_wellord2(esk5_0),k1_wellord1(k1_wellord2(esk5_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_30]),c_0_28])])).

cnf(c_0_50,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ r4_wellord1(k1_wellord2(esk5_0),k2_wellord1(k1_wellord2(esk5_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( k2_wellord1(k1_wellord2(esk5_0),esk4_0) = k1_wellord2(esk4_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_21]),c_0_21])])).

cnf(c_0_57,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_59,negated_conjecture,
    ( k3_relat_1(k2_wellord1(k1_wellord2(esk4_0),k1_wellord1(k1_wellord2(esk4_0),X1))) = k1_wellord1(k1_wellord2(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk4_0),esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_58]),c_0_25]),c_0_19])])).

cnf(c_0_61,negated_conjecture,
    ( k3_relat_1(k2_wellord1(k1_wellord2(esk4_0),esk5_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_61]),c_0_39]),c_0_21])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),esk4_0)
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_43])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_58]),c_0_57])]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k2_wellord1(k1_wellord2(esk4_0),esk5_0) = k1_wellord2(esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
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
% 0.20/0.38  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.20/0.38  fof(t40_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v2_wellord1(X2)=>k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1)))=k1_wellord1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_wellord1)).
% 0.20/0.38  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.20/0.38  fof(t7_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 0.20/0.38  fof(t10_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>X1=k1_wellord1(k1_wellord2(X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 0.20/0.38  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.20/0.38  fof(t19_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_wellord1)).
% 0.20/0.38  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 0.20/0.38  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 0.20/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2)))), inference(assume_negation,[status(cth)],[t11_wellord2])).
% 0.20/0.38  fof(c_0_13, plain, ![X11, X12]:(~v3_ordinal1(X11)|(~v3_ordinal1(X12)|(r2_hidden(X11,X12)|X11=X12|r2_hidden(X12,X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.20/0.38  fof(c_0_14, negated_conjecture, (v3_ordinal1(esk4_0)&(v3_ordinal1(esk5_0)&(r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))&esk4_0!=esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.38  fof(c_0_15, plain, ![X16, X17]:(~v1_relat_1(X17)|(~v2_wellord1(X17)|k3_relat_1(k2_wellord1(X17,k1_wellord1(X17,X16)))=k1_wellord1(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_wellord1])])).
% 0.20/0.38  fof(c_0_16, plain, ![X28]:v1_relat_1(k1_wellord2(X28)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.20/0.38  fof(c_0_17, plain, ![X31]:(~v3_ordinal1(X31)|v2_wellord1(k1_wellord2(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).
% 0.20/0.38  cnf(c_0_18, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_20, plain, (k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2)))=k1_wellord1(X1,X2)|~v1_relat_1(X1)|~v2_wellord1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_21, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_22, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  fof(c_0_23, plain, ![X29, X30]:(~v3_ordinal1(X29)|(~v3_ordinal1(X30)|(~r2_hidden(X29,X30)|X29=k1_wellord1(k1_wellord2(X30),X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (X1=esk5_0|r2_hidden(X1,esk5_0)|r2_hidden(esk5_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_27, plain, (k3_relat_1(k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X2)))=k1_wellord1(k1_wellord2(X1),X2)|~v2_wellord1(k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (v2_wellord1(k1_wellord2(esk5_0))), inference(spm,[status(thm)],[c_0_22, c_0_19])).
% 0.20/0.38  cnf(c_0_29, plain, (X1=k1_wellord1(k1_wellord2(X2),X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.20/0.38  fof(c_0_31, plain, ![X22, X23, X24, X25]:(((k3_relat_1(X23)=X22|X23!=k1_wellord2(X22)|~v1_relat_1(X23))&((~r2_hidden(k4_tarski(X24,X25),X23)|r1_tarski(X24,X25)|(~r2_hidden(X24,X22)|~r2_hidden(X25,X22))|X23!=k1_wellord2(X22)|~v1_relat_1(X23))&(~r1_tarski(X24,X25)|r2_hidden(k4_tarski(X24,X25),X23)|(~r2_hidden(X24,X22)|~r2_hidden(X25,X22))|X23!=k1_wellord2(X22)|~v1_relat_1(X23))))&(((r2_hidden(esk2_2(X22,X23),X22)|k3_relat_1(X23)!=X22|X23=k1_wellord2(X22)|~v1_relat_1(X23))&(r2_hidden(esk3_2(X22,X23),X22)|k3_relat_1(X23)!=X22|X23=k1_wellord2(X22)|~v1_relat_1(X23)))&((~r2_hidden(k4_tarski(esk2_2(X22,X23),esk3_2(X22,X23)),X23)|~r1_tarski(esk2_2(X22,X23),esk3_2(X22,X23))|k3_relat_1(X23)!=X22|X23=k1_wellord2(X22)|~v1_relat_1(X23))&(r2_hidden(k4_tarski(esk2_2(X22,X23),esk3_2(X22,X23)),X23)|r1_tarski(esk2_2(X22,X23),esk3_2(X22,X23))|k3_relat_1(X23)!=X22|X23=k1_wellord2(X22)|~v1_relat_1(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.20/0.38  fof(c_0_32, plain, ![X13, X14, X15]:((r2_hidden(X13,k3_relat_1(X15))|~r2_hidden(X13,k3_relat_1(k2_wellord1(X15,X14)))|~v1_relat_1(X15))&(r2_hidden(X13,X14)|~r2_hidden(X13,k3_relat_1(k2_wellord1(X15,X14)))|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (k3_relat_1(k2_wellord1(k1_wellord2(esk5_0),k1_wellord1(k1_wellord2(esk5_0),X1)))=k1_wellord1(k1_wellord2(esk5_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (k1_wellord1(k1_wellord2(esk5_0),esk4_0)=esk4_0|r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_19]), c_0_25])])).
% 0.20/0.38  cnf(c_0_35, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  fof(c_0_36, plain, ![X20, X21]:(~v1_relat_1(X20)|(~v2_wellord1(X20)|(~r2_hidden(X21,k3_relat_1(X20))|~r4_wellord1(X20,k2_wellord1(X20,k1_wellord1(X20,X21)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.20/0.38  cnf(c_0_37, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (k3_relat_1(k2_wellord1(k1_wellord2(esk5_0),esk4_0))=esk4_0|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.38  cnf(c_0_39, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_35]), c_0_21])])).
% 0.20/0.38  fof(c_0_40, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_41, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_21])])).
% 0.20/0.38  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  cnf(c_0_44, plain, (~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X2)))|~v2_wellord1(k1_wellord2(X1))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_39]), c_0_21])])).
% 0.20/0.38  fof(c_0_45, plain, ![X32, X33]:(~r1_tarski(X32,X33)|k2_wellord1(k1_wellord2(X33),X32)=k1_wellord2(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.20/0.38  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk5_0)|r2_hidden(esk5_0,esk4_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.38  fof(c_0_48, plain, ![X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|(~r4_wellord1(X18,X19)|r4_wellord1(X19,X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~r4_wellord1(k1_wellord2(esk5_0),k2_wellord1(k1_wellord2(esk5_0),k1_wellord1(k1_wellord2(esk5_0),esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_30]), c_0_28])])).
% 0.20/0.38  cnf(c_0_50, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.38  cnf(c_0_52, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~r4_wellord1(k1_wellord2(esk5_0),k2_wellord1(k1_wellord2(esk5_0),esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_34])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (k2_wellord1(k1_wellord2(esk5_0),esk4_0)=k1_wellord2(esk4_0)|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_21]), c_0_21])])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (v2_wellord1(k1_wellord2(esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_25])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (k3_relat_1(k2_wellord1(k1_wellord2(esk4_0),k1_wellord1(k1_wellord2(esk4_0),X1)))=k1_wellord1(k1_wellord2(esk4_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_57])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (k1_wellord1(k1_wellord2(esk4_0),esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_58]), c_0_25]), c_0_19])])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (k3_relat_1(k2_wellord1(k1_wellord2(esk4_0),esk5_0))=esk5_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_61]), c_0_39]), c_0_21])])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),esk4_0)|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_43])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_63])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (~r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),esk5_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_58]), c_0_57])]), c_0_60])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (k2_wellord1(k1_wellord2(esk4_0),esk5_0)=k1_wellord2(esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_64])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66]), c_0_53])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 68
% 0.20/0.38  # Proof object clause steps            : 43
% 0.20/0.38  # Proof object formula steps           : 25
% 0.20/0.38  # Proof object conjectures             : 31
% 0.20/0.38  # Proof object clause conjectures      : 28
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 16
% 0.20/0.38  # Proof object initial formulas used   : 12
% 0.20/0.38  # Proof object generating inferences   : 25
% 0.20/0.38  # Proof object simplifying inferences  : 31
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 12
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 24
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 24
% 0.20/0.38  # Processed clauses                    : 100
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 3
% 0.20/0.38  # ...remaining for further processing  : 97
% 0.20/0.38  # Other redundant clauses eliminated   : 7
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 12
% 0.20/0.38  # Generated clauses                    : 106
% 0.20/0.38  # ...of the previous two non-trivial   : 88
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 99
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 7
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
% 0.20/0.38  # Current number of processed clauses  : 54
% 0.20/0.38  #    Positive orientable unit clauses  : 18
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 35
% 0.20/0.38  # Current number of unprocessed clauses: 33
% 0.20/0.38  # ...number of literals in the above   : 114
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 36
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 220
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 125
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.20/0.38  # Unit Clause-clause subsumption calls : 49
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 9
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 4406
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.033 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
