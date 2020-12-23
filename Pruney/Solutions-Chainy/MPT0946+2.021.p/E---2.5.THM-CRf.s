%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 (2358 expanded)
%              Number of clauses        :   61 ( 998 expanded)
%              Number of leaves         :   12 ( 603 expanded)
%              Depth                    :   23
%              Number of atoms          :  341 (10302 expanded)
%              Number of equality atoms :   74 (2435 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   33 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(t51_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ? [X2] :
          ( v3_ordinal1(X2)
          & r2_hidden(X1,X2)
          & v4_ordinal1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_ordinal1)).

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

fof(c_0_12,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( X15 != X13
        | ~ r2_hidden(X15,X14)
        | X14 != k1_wellord1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(X15,X13),X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k1_wellord1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( X16 = X13
        | ~ r2_hidden(k4_tarski(X16,X13),X12)
        | r2_hidden(X16,X14)
        | X14 != k1_wellord1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(esk2_3(X12,X17,X18),X18)
        | esk2_3(X12,X17,X18) = X17
        | ~ r2_hidden(k4_tarski(esk2_3(X12,X17,X18),X17),X12)
        | X18 = k1_wellord1(X12,X17)
        | ~ v1_relat_1(X12) )
      & ( esk2_3(X12,X17,X18) != X17
        | r2_hidden(esk2_3(X12,X17,X18),X18)
        | X18 = k1_wellord1(X12,X17)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk2_3(X12,X17,X18),X17),X12)
        | r2_hidden(esk2_3(X12,X17,X18),X18)
        | X18 = k1_wellord1(X12,X17)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

fof(c_0_13,plain,(
    ! [X5,X6,X7] :
      ( ( r2_hidden(X5,k3_relat_1(X7))
        | ~ r2_hidden(k4_tarski(X5,X6),X7)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(X6,k3_relat_1(X7))
        | ~ r2_hidden(k4_tarski(X5,X6),X7)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X24,X25,X26,X27] :
      ( ( k3_relat_1(X25) = X24
        | X25 != k1_wellord2(X24)
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(k4_tarski(X26,X27),X25)
        | r1_tarski(X26,X27)
        | ~ r2_hidden(X26,X24)
        | ~ r2_hidden(X27,X24)
        | X25 != k1_wellord2(X24)
        | ~ v1_relat_1(X25) )
      & ( ~ r1_tarski(X26,X27)
        | r2_hidden(k4_tarski(X26,X27),X25)
        | ~ r2_hidden(X26,X24)
        | ~ r2_hidden(X27,X24)
        | X25 != k1_wellord2(X24)
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(esk3_2(X24,X25),X24)
        | k3_relat_1(X25) != X24
        | X25 = k1_wellord2(X24)
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(esk4_2(X24,X25),X24)
        | k3_relat_1(X25) != X24
        | X25 = k1_wellord2(X24)
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X24,X25),esk4_2(X24,X25)),X25)
        | ~ r1_tarski(esk3_2(X24,X25),esk4_2(X24,X25))
        | k3_relat_1(X25) != X24
        | X25 = k1_wellord2(X24)
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(k4_tarski(esk3_2(X24,X25),esk4_2(X24,X25)),X25)
        | r1_tarski(esk3_2(X24,X25),esk4_2(X24,X25))
        | k3_relat_1(X25) != X24
        | X25 = k1_wellord2(X24)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_16,plain,(
    ! [X30] : v1_relat_1(k1_wellord2(X30)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord2])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X31,X32] :
      ( ~ v3_ordinal1(X31)
      | ~ v3_ordinal1(X32)
      | ~ r2_hidden(X31,X32)
      | X31 = k1_wellord1(k1_wellord2(X32),X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

cnf(c_0_21,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X8,X9] :
      ( ~ v3_ordinal1(X8)
      | ~ v3_ordinal1(X9)
      | r2_hidden(X8,X9)
      | X8 = X9
      | r2_hidden(X9,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_24,negated_conjecture,
    ( v3_ordinal1(esk5_0)
    & v3_ordinal1(esk6_0)
    & r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk6_0))
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22])])).

fof(c_0_28,plain,(
    ! [X10] :
      ( ( v3_ordinal1(esk1_1(X10))
        | ~ v3_ordinal1(X10) )
      & ( r2_hidden(X10,esk1_1(X10))
        | ~ v3_ordinal1(X10) )
      & ( v4_ordinal1(esk1_1(X10))
        | ~ v3_ordinal1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_ordinal1])])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ v2_wellord1(X22)
      | ~ r2_hidden(X23,k3_relat_1(X22))
      | ~ r4_wellord1(X22,k2_wellord1(X22,k1_wellord1(X22,X23))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

fof(c_0_32,plain,(
    ! [X33] :
      ( ~ v3_ordinal1(X33)
      | v2_wellord1(k1_wellord2(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X3)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_22])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,esk1_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( v3_ordinal1(esk1_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(esk5_0,X1)
    | r2_hidden(X1,esk5_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v3_ordinal1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X34,X35] :
      ( ~ r1_tarski(X34,X35)
      | k2_wellord1(k1_wellord2(X35),X34) = k1_wellord2(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_22])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk1_1(X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( esk1_1(X1) = esk5_0
    | r2_hidden(esk1_1(X1),esk5_0)
    | r2_hidden(esk5_0,esk1_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(esk6_0,X1)
    | r2_hidden(X1,esk6_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_46,plain,
    ( ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_22])]),c_0_27])]),c_0_40])).

cnf(c_0_47,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_wellord1(k1_wellord2(X3),X2))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_22])])).

cnf(c_0_49,negated_conjecture,
    ( esk1_1(X1) = esk5_0
    | r2_hidden(esk5_0,esk1_1(X1))
    | r2_hidden(X1,esk5_0)
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_30])])).

fof(c_0_50,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | ~ r4_wellord1(X20,X21)
      | r4_wellord1(X21,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_51,negated_conjecture,
    ( esk1_1(X1) = esk6_0
    | r2_hidden(esk1_1(X1),esk6_0)
    | r2_hidden(esk6_0,esk1_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_36])).

cnf(c_0_52,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r4_wellord1(k1_wellord2(X2),k1_wellord2(X1))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ v3_ordinal1(X3)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_26]),c_0_34])).

cnf(c_0_56,negated_conjecture,
    ( esk1_1(esk5_0) = esk5_0
    | r2_hidden(esk5_0,esk1_1(esk5_0))
    | r2_hidden(esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_30])).

cnf(c_0_57,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( esk1_1(X1) = esk6_0
    | r2_hidden(esk6_0,esk1_1(X1))
    | r2_hidden(X1,esk6_0)
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_51]),c_0_38])])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k1_wellord1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(esk6_0,esk5_0)
    | ~ r2_hidden(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_30]),c_0_38])])).

cnf(c_0_61,negated_conjecture,
    ( esk1_1(esk5_0) = esk5_0
    | r1_tarski(X1,esk5_0)
    | r2_hidden(esk5_0,esk5_0)
    | ~ v3_ordinal1(esk1_1(esk5_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_30])])).

cnf(c_0_62,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_54]),c_0_22]),c_0_22])])).

cnf(c_0_63,negated_conjecture,
    ( esk1_1(esk6_0) = esk6_0
    | r2_hidden(esk6_0,esk1_1(esk6_0))
    | r2_hidden(esk6_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_38])).

cnf(c_0_64,plain,
    ( ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_26]),c_0_22])])).

cnf(c_0_65,negated_conjecture,
    ( esk1_1(esk5_0) = esk5_0
    | r2_hidden(esk5_0,esk5_0)
    | ~ v3_ordinal1(esk1_1(esk5_0))
    | ~ r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_62]),c_0_38]),c_0_30])])).

cnf(c_0_67,negated_conjecture,
    ( esk1_1(esk6_0) = esk6_0
    | r1_tarski(X1,esk6_0)
    | r2_hidden(esk6_0,esk6_0)
    | ~ v3_ordinal1(esk1_1(esk6_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_63]),c_0_38])])).

cnf(c_0_68,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_69,negated_conjecture,
    ( esk1_1(esk5_0) = esk5_0
    | ~ v3_ordinal1(esk1_1(esk5_0))
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk6_0,esk5_0)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_30])])).

cnf(c_0_70,negated_conjecture,
    ( esk1_1(esk6_0) = esk6_0
    | r2_hidden(esk6_0,esk6_0)
    | ~ v3_ordinal1(esk1_1(esk6_0))
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | r2_hidden(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_30]),c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( esk1_1(esk5_0) = esk5_0
    | ~ v3_ordinal1(esk1_1(esk5_0))
    | ~ r2_hidden(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_35]),c_0_30])])).

cnf(c_0_73,negated_conjecture,
    ( esk1_1(esk6_0) = esk6_0
    | r2_hidden(esk6_0,esk5_0)
    | r2_hidden(esk6_0,esk6_0)
    | ~ v3_ordinal1(esk1_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( esk1_1(esk6_0) = esk6_0
    | esk1_1(esk5_0) = esk5_0
    | r2_hidden(esk6_0,esk6_0)
    | ~ v3_ordinal1(esk1_1(esk5_0))
    | ~ v3_ordinal1(esk1_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_75,negated_conjecture,
    ( esk1_1(esk5_0) = esk5_0
    | esk1_1(esk6_0) = esk6_0
    | ~ v3_ordinal1(esk1_1(esk5_0))
    | ~ v3_ordinal1(esk1_1(esk6_0))
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_74]),c_0_38])])).

cnf(c_0_76,negated_conjecture,
    ( esk1_1(esk6_0) = esk6_0
    | esk1_1(esk5_0) = esk5_0
    | ~ v3_ordinal1(esk1_1(esk5_0))
    | ~ v3_ordinal1(esk1_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_35]),c_0_38])])).

cnf(c_0_77,negated_conjecture,
    ( esk1_1(esk5_0) = esk5_0
    | esk1_1(esk6_0) = esk6_0
    | ~ v3_ordinal1(esk1_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_36]),c_0_30])])).

cnf(c_0_78,negated_conjecture,
    ( esk1_1(esk6_0) = esk6_0
    | esk1_1(esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_36]),c_0_38])])).

cnf(c_0_79,negated_conjecture,
    ( esk1_1(esk6_0) = esk6_0
    | r2_hidden(esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_78]),c_0_30])])).

cnf(c_0_80,negated_conjecture,
    ( esk1_1(esk6_0) = esk6_0
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_79]),c_0_30])])).

cnf(c_0_81,negated_conjecture,
    ( esk1_1(esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_79]),c_0_30])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_81]),c_0_38])])).

cnf(c_0_83,negated_conjecture,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_82]),c_0_38])])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,esk1_1(esk1_1(X1)))
    | ~ v3_ordinal1(esk1_1(esk1_1(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_35]),c_0_36])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_81]),c_0_81]),c_0_38]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:39:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.20/0.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.028 s
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 0.20/0.42  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 0.20/0.42  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.20/0.42  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.20/0.42  fof(t11_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 0.20/0.42  fof(t10_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>X1=k1_wellord1(k1_wellord2(X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 0.20/0.42  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.20/0.42  fof(t51_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>?[X2]:((v3_ordinal1(X2)&r2_hidden(X1,X2))&v4_ordinal1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_ordinal1)).
% 0.20/0.42  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 0.20/0.42  fof(t7_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 0.20/0.42  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 0.20/0.42  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 0.20/0.42  fof(c_0_12, plain, ![X12, X13, X14, X15, X16, X17, X18]:((((X15!=X13|~r2_hidden(X15,X14)|X14!=k1_wellord1(X12,X13)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(X15,X13),X12)|~r2_hidden(X15,X14)|X14!=k1_wellord1(X12,X13)|~v1_relat_1(X12)))&(X16=X13|~r2_hidden(k4_tarski(X16,X13),X12)|r2_hidden(X16,X14)|X14!=k1_wellord1(X12,X13)|~v1_relat_1(X12)))&((~r2_hidden(esk2_3(X12,X17,X18),X18)|(esk2_3(X12,X17,X18)=X17|~r2_hidden(k4_tarski(esk2_3(X12,X17,X18),X17),X12))|X18=k1_wellord1(X12,X17)|~v1_relat_1(X12))&((esk2_3(X12,X17,X18)!=X17|r2_hidden(esk2_3(X12,X17,X18),X18)|X18=k1_wellord1(X12,X17)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(esk2_3(X12,X17,X18),X17),X12)|r2_hidden(esk2_3(X12,X17,X18),X18)|X18=k1_wellord1(X12,X17)|~v1_relat_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.20/0.42  fof(c_0_13, plain, ![X5, X6, X7]:((r2_hidden(X5,k3_relat_1(X7))|~r2_hidden(k4_tarski(X5,X6),X7)|~v1_relat_1(X7))&(r2_hidden(X6,k3_relat_1(X7))|~r2_hidden(k4_tarski(X5,X6),X7)|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.20/0.42  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  fof(c_0_15, plain, ![X24, X25, X26, X27]:(((k3_relat_1(X25)=X24|X25!=k1_wellord2(X24)|~v1_relat_1(X25))&((~r2_hidden(k4_tarski(X26,X27),X25)|r1_tarski(X26,X27)|(~r2_hidden(X26,X24)|~r2_hidden(X27,X24))|X25!=k1_wellord2(X24)|~v1_relat_1(X25))&(~r1_tarski(X26,X27)|r2_hidden(k4_tarski(X26,X27),X25)|(~r2_hidden(X26,X24)|~r2_hidden(X27,X24))|X25!=k1_wellord2(X24)|~v1_relat_1(X25))))&(((r2_hidden(esk3_2(X24,X25),X24)|k3_relat_1(X25)!=X24|X25=k1_wellord2(X24)|~v1_relat_1(X25))&(r2_hidden(esk4_2(X24,X25),X24)|k3_relat_1(X25)!=X24|X25=k1_wellord2(X24)|~v1_relat_1(X25)))&((~r2_hidden(k4_tarski(esk3_2(X24,X25),esk4_2(X24,X25)),X25)|~r1_tarski(esk3_2(X24,X25),esk4_2(X24,X25))|k3_relat_1(X25)!=X24|X25=k1_wellord2(X24)|~v1_relat_1(X25))&(r2_hidden(k4_tarski(esk3_2(X24,X25),esk4_2(X24,X25)),X25)|r1_tarski(esk3_2(X24,X25),esk4_2(X24,X25))|k3_relat_1(X25)!=X24|X25=k1_wellord2(X24)|~v1_relat_1(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.20/0.42  fof(c_0_16, plain, ![X30]:v1_relat_1(k1_wellord2(X30)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.20/0.42  fof(c_0_17, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2)))), inference(assume_negation,[status(cth)],[t11_wellord2])).
% 0.20/0.42  cnf(c_0_18, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_14])).
% 0.20/0.42  fof(c_0_20, plain, ![X31, X32]:(~v3_ordinal1(X31)|(~v3_ordinal1(X32)|(~r2_hidden(X31,X32)|X31=k1_wellord1(k1_wellord2(X32),X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).
% 0.20/0.42  cnf(c_0_21, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_22, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  fof(c_0_23, plain, ![X8, X9]:(~v3_ordinal1(X8)|(~v3_ordinal1(X9)|(r2_hidden(X8,X9)|X8=X9|r2_hidden(X9,X8)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.20/0.42  fof(c_0_24, negated_conjecture, (v3_ordinal1(esk5_0)&(v3_ordinal1(esk6_0)&(r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk6_0))&esk5_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.20/0.42  cnf(c_0_25, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(X1,k1_wellord1(X2,X3))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.42  cnf(c_0_26, plain, (X1=k1_wellord1(k1_wellord2(X2),X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_27, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_21]), c_0_22])])).
% 0.20/0.42  fof(c_0_28, plain, ![X10]:(((v3_ordinal1(esk1_1(X10))|~v3_ordinal1(X10))&(r2_hidden(X10,esk1_1(X10))|~v3_ordinal1(X10)))&(v4_ordinal1(esk1_1(X10))|~v3_ordinal1(X10))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_ordinal1])])])])).
% 0.20/0.42  cnf(c_0_29, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  fof(c_0_31, plain, ![X22, X23]:(~v1_relat_1(X22)|(~v2_wellord1(X22)|(~r2_hidden(X23,k3_relat_1(X22))|~r4_wellord1(X22,k2_wellord1(X22,k1_wellord1(X22,X23)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.20/0.42  fof(c_0_32, plain, ![X33]:(~v3_ordinal1(X33)|v2_wellord1(k1_wellord2(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).
% 0.20/0.42  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X3)|~r2_hidden(X1,X3)|~r2_hidden(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_22])])).
% 0.20/0.42  cnf(c_0_35, plain, (r2_hidden(X1,esk1_1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.42  cnf(c_0_36, plain, (v3_ordinal1(esk1_1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (X1=esk5_0|r2_hidden(esk5_0,X1)|r2_hidden(X1,esk5_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (v3_ordinal1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_39, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_40, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  fof(c_0_41, plain, ![X34, X35]:(~r1_tarski(X34,X35)|k2_wellord1(k1_wellord2(X35),X34)=k1_wellord2(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.20/0.42  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]), c_0_22])])).
% 0.20/0.42  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(esk1_1(X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.20/0.42  cnf(c_0_44, negated_conjecture, (esk1_1(X1)=esk5_0|r2_hidden(esk1_1(X1),esk5_0)|r2_hidden(esk5_0,esk1_1(X1))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 0.20/0.42  cnf(c_0_45, negated_conjecture, (X1=esk6_0|r2_hidden(esk6_0,X1)|r2_hidden(X1,esk6_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_38])).
% 0.20/0.42  cnf(c_0_46, plain, (~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_26]), c_0_22])]), c_0_27])]), c_0_40])).
% 0.20/0.42  cnf(c_0_47, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.42  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_wellord1(k1_wellord2(X3),X2))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_19]), c_0_22])])).
% 0.20/0.42  cnf(c_0_49, negated_conjecture, (esk1_1(X1)=esk5_0|r2_hidden(esk5_0,esk1_1(X1))|r2_hidden(X1,esk5_0)|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_30])])).
% 0.20/0.42  fof(c_0_50, plain, ![X20, X21]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|(~r4_wellord1(X20,X21)|r4_wellord1(X21,X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (esk1_1(X1)=esk6_0|r2_hidden(esk1_1(X1),esk6_0)|r2_hidden(esk6_0,esk1_1(X1))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_36])).
% 0.20/0.42  cnf(c_0_52, plain, (X1!=X2|~r2_hidden(X1,X3)|X3!=k1_wellord1(X4,X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_53, plain, (~r1_tarski(X1,X2)|~r4_wellord1(k1_wellord2(X2),k1_wellord2(X1))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.42  cnf(c_0_54, negated_conjecture, (r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~v3_ordinal1(X3)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_26]), c_0_34])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (esk1_1(esk5_0)=esk5_0|r2_hidden(esk5_0,esk1_1(esk5_0))|r2_hidden(esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_49, c_0_30])).
% 0.20/0.42  cnf(c_0_57, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (esk1_1(X1)=esk6_0|r2_hidden(esk6_0,esk1_1(X1))|r2_hidden(X1,esk6_0)|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_51]), c_0_38])])).
% 0.20/0.42  cnf(c_0_59, plain, (~r2_hidden(X1,k1_wellord1(X2,X1))|~v1_relat_1(X2)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).
% 0.20/0.42  cnf(c_0_60, negated_conjecture, (~r1_tarski(esk6_0,esk5_0)|~r2_hidden(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_30]), c_0_38])])).
% 0.20/0.42  cnf(c_0_61, negated_conjecture, (esk1_1(esk5_0)=esk5_0|r1_tarski(X1,esk5_0)|r2_hidden(esk5_0,esk5_0)|~v3_ordinal1(esk1_1(esk5_0))|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_30])])).
% 0.20/0.42  cnf(c_0_62, negated_conjecture, (r4_wellord1(k1_wellord2(esk6_0),k1_wellord2(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_54]), c_0_22]), c_0_22])])).
% 0.20/0.42  cnf(c_0_63, negated_conjecture, (esk1_1(esk6_0)=esk6_0|r2_hidden(esk6_0,esk1_1(esk6_0))|r2_hidden(esk6_0,esk6_0)), inference(spm,[status(thm)],[c_0_58, c_0_38])).
% 0.20/0.42  cnf(c_0_64, plain, (~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X2,X2)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_26]), c_0_22])])).
% 0.20/0.42  cnf(c_0_65, negated_conjecture, (esk1_1(esk5_0)=esk5_0|r2_hidden(esk5_0,esk5_0)|~v3_ordinal1(esk1_1(esk5_0))|~r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (~r1_tarski(esk5_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_62]), c_0_38]), c_0_30])])).
% 0.20/0.42  cnf(c_0_67, negated_conjecture, (esk1_1(esk6_0)=esk6_0|r1_tarski(X1,esk6_0)|r2_hidden(esk6_0,esk6_0)|~v3_ordinal1(esk1_1(esk6_0))|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_63]), c_0_38])])).
% 0.20/0.42  cnf(c_0_68, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_69, negated_conjecture, (esk1_1(esk5_0)=esk5_0|~v3_ordinal1(esk1_1(esk5_0))|~v3_ordinal1(X1)|~r2_hidden(esk6_0,esk5_0)|~r2_hidden(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_30])])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (esk1_1(esk6_0)=esk6_0|r2_hidden(esk6_0,esk6_0)|~v3_ordinal1(esk1_1(esk6_0))|~r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.42  cnf(c_0_71, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|r2_hidden(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_30]), c_0_68])).
% 0.20/0.42  cnf(c_0_72, negated_conjecture, (esk1_1(esk5_0)=esk5_0|~v3_ordinal1(esk1_1(esk5_0))|~r2_hidden(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_35]), c_0_30])])).
% 0.20/0.42  cnf(c_0_73, negated_conjecture, (esk1_1(esk6_0)=esk6_0|r2_hidden(esk6_0,esk5_0)|r2_hidden(esk6_0,esk6_0)|~v3_ordinal1(esk1_1(esk6_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.42  cnf(c_0_74, negated_conjecture, (esk1_1(esk6_0)=esk6_0|esk1_1(esk5_0)=esk5_0|r2_hidden(esk6_0,esk6_0)|~v3_ordinal1(esk1_1(esk5_0))|~v3_ordinal1(esk1_1(esk6_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.42  cnf(c_0_75, negated_conjecture, (esk1_1(esk5_0)=esk5_0|esk1_1(esk6_0)=esk6_0|~v3_ordinal1(esk1_1(esk5_0))|~v3_ordinal1(esk1_1(esk6_0))|~v3_ordinal1(X1)|~r2_hidden(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_74]), c_0_38])])).
% 0.20/0.42  cnf(c_0_76, negated_conjecture, (esk1_1(esk6_0)=esk6_0|esk1_1(esk5_0)=esk5_0|~v3_ordinal1(esk1_1(esk5_0))|~v3_ordinal1(esk1_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_35]), c_0_38])])).
% 0.20/0.42  cnf(c_0_77, negated_conjecture, (esk1_1(esk5_0)=esk5_0|esk1_1(esk6_0)=esk6_0|~v3_ordinal1(esk1_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_36]), c_0_30])])).
% 0.20/0.42  cnf(c_0_78, negated_conjecture, (esk1_1(esk6_0)=esk6_0|esk1_1(esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_36]), c_0_38])])).
% 0.20/0.42  cnf(c_0_79, negated_conjecture, (esk1_1(esk6_0)=esk6_0|r2_hidden(esk5_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_78]), c_0_30])])).
% 0.20/0.42  cnf(c_0_80, negated_conjecture, (esk1_1(esk6_0)=esk6_0|~v3_ordinal1(X1)|~r2_hidden(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_79]), c_0_30])])).
% 0.20/0.42  cnf(c_0_81, negated_conjecture, (esk1_1(esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_79]), c_0_30])])).
% 0.20/0.42  cnf(c_0_82, negated_conjecture, (r2_hidden(esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_81]), c_0_38])])).
% 0.20/0.42  cnf(c_0_83, negated_conjecture, (~v3_ordinal1(X1)|~r2_hidden(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_82]), c_0_38])])).
% 0.20/0.42  cnf(c_0_84, plain, (r2_hidden(X1,esk1_1(esk1_1(X1)))|~v3_ordinal1(esk1_1(esk1_1(X1)))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_35]), c_0_36])).
% 0.20/0.42  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_81]), c_0_81]), c_0_38]), c_0_38])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 86
% 0.20/0.42  # Proof object clause steps            : 61
% 0.20/0.42  # Proof object formula steps           : 25
% 0.20/0.42  # Proof object conjectures             : 37
% 0.20/0.42  # Proof object clause conjectures      : 34
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 18
% 0.20/0.42  # Proof object initial formulas used   : 12
% 0.20/0.42  # Proof object generating inferences   : 39
% 0.20/0.42  # Proof object simplifying inferences  : 69
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 12
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 29
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 29
% 0.20/0.42  # Processed clauses                    : 262
% 0.20/0.42  # ...of these trivial                  : 0
% 0.20/0.42  # ...subsumed                          : 69
% 0.20/0.42  # ...remaining for further processing  : 193
% 0.20/0.42  # Other redundant clauses eliminated   : 11
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 25
% 0.20/0.42  # Backward-rewritten                   : 35
% 0.20/0.42  # Generated clauses                    : 856
% 0.20/0.42  # ...of the previous two non-trivial   : 782
% 0.20/0.42  # Contextual simplify-reflections      : 22
% 0.20/0.42  # Paramodulations                      : 846
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 11
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 123
% 0.20/0.42  #    Positive orientable unit clauses  : 9
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 1
% 0.20/0.42  #    Non-unit-clauses                  : 113
% 0.20/0.42  # Current number of unprocessed clauses: 532
% 0.20/0.42  # ...number of literals in the above   : 3299
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 60
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 14645
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 1394
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 116
% 0.20/0.42  # Unit Clause-clause subsumption calls : 313
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 1
% 0.20/0.42  # BW rewrite match successes           : 1
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 24103
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.063 s
% 0.20/0.42  # System time              : 0.005 s
% 0.20/0.42  # Total time               : 0.068 s
% 0.20/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
