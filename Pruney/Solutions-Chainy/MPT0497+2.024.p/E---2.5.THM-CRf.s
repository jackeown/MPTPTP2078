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
% DateTime   : Thu Dec  3 10:49:36 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 471 expanded)
%              Number of clauses        :   54 ( 220 expanded)
%              Number of leaves         :   14 ( 121 expanded)
%              Depth                    :   13
%              Number of atoms          :  182 (1120 expanded)
%              Number of equality atoms :   54 ( 331 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t95_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_14,plain,(
    ! [X25,X26] : k1_setfam_1(k2_tarski(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_21,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_22,plain,(
    ! [X16,X17] : r1_xboole_0(k4_xboole_0(X16,X17),X17) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_23,plain,(
    ! [X30,X31,X32] :
      ( ( r2_hidden(X30,X31)
        | ~ r2_hidden(X30,k1_relat_1(k7_relat_1(X32,X31)))
        | ~ v1_relat_1(X32) )
      & ( r2_hidden(X30,k1_relat_1(X32))
        | ~ r2_hidden(X30,k1_relat_1(k7_relat_1(X32,X31)))
        | ~ v1_relat_1(X32) )
      & ( ~ r2_hidden(X30,X31)
        | ~ r2_hidden(X30,k1_relat_1(X32))
        | r2_hidden(X30,k1_relat_1(k7_relat_1(X32,X31)))
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

fof(c_0_24,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k7_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t95_relat_1])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X18,X19] :
      ( ( ~ r1_xboole_0(X18,X19)
        | k4_xboole_0(X18,X19) = X18 )
      & ( k4_xboole_0(X18,X19) != X18
        | r1_xboole_0(X18,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ( k7_relat_1(esk3_0,esk2_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk3_0),esk2_0) )
    & ( k7_relat_1(esk3_0,esk2_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk3_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_27]),c_0_28])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),X3)
    | r1_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(esk3_0,X2))),X2)
    | r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),k1_relat_1(X2))
    | r1_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_34])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_34])).

cnf(c_0_52,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk3_0,X2)))
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(esk3_0,X2))),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(esk3_0,X2))),k1_relat_1(esk3_0))
    | r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_42])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_2(X1,k1_relat_1(X2)),k1_relat_1(k7_relat_1(X2,X3)))
    | r1_xboole_0(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(X2)),X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_34])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_57,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_27]),c_0_28])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk3_0,X2)))
    | ~ r1_xboole_0(k1_relat_1(esk3_0),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k7_relat_1(esk3_0,esk2_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_2(X1,k1_relat_1(X2)),k1_relat_1(k7_relat_1(X2,X1)))
    | r1_xboole_0(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_38])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( k7_relat_1(esk3_0,esk2_0) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_65,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | v1_relat_1(k7_relat_1(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk1_2(X1,k1_relat_1(esk3_0)),k1_relat_1(k7_relat_1(esk3_0,X1)))
    | r1_xboole_0(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_42])).

fof(c_0_67,plain,(
    ! [X29] :
      ( ( k1_relat_1(X29) != k1_xboole_0
        | X29 = k1_xboole_0
        | ~ v1_relat_1(X29) )
      & ( k2_relat_1(X29) != k1_xboole_0
        | X29 = k1_xboole_0
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_58]),c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(X1,k1_relat_1(k7_relat_1(esk3_0,esk2_0))) = X1
    | k7_relat_1(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_64])).

cnf(c_0_70,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(X1,k1_relat_1(esk3_0))
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(esk3_0)),X2)
    | ~ r1_xboole_0(X2,k1_relat_1(k7_relat_1(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_66])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,esk2_0)) = k1_xboole_0
    | k7_relat_1(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_42])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(X1,k1_relat_1(esk3_0))
    | ~ r1_xboole_0(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_34])).

cnf(c_0_76,negated_conjecture,
    ( k7_relat_1(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])])).

cnf(c_0_77,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_78,negated_conjecture,
    ( k7_relat_1(esk3_0,esk2_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_79,negated_conjecture,
    ( r1_xboole_0(esk2_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_58])])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_76])])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_79]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n007.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 10:28:36 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.13/0.38  # and selection function SelectLComplex.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.38  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.13/0.38  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 0.13/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.38  fof(t95_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 0.13/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.13/0.38  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.13/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.38  fof(c_0_14, plain, ![X25, X26]:k1_setfam_1(k2_tarski(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.38  fof(c_0_15, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_16, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.13/0.38  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_19, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_20, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.38  fof(c_0_21, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.38  fof(c_0_22, plain, ![X16, X17]:r1_xboole_0(k4_xboole_0(X16,X17),X17), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.13/0.38  fof(c_0_23, plain, ![X30, X31, X32]:(((r2_hidden(X30,X31)|~r2_hidden(X30,k1_relat_1(k7_relat_1(X32,X31)))|~v1_relat_1(X32))&(r2_hidden(X30,k1_relat_1(X32))|~r2_hidden(X30,k1_relat_1(k7_relat_1(X32,X31)))|~v1_relat_1(X32)))&(~r2_hidden(X30,X31)|~r2_hidden(X30,k1_relat_1(X32))|r2_hidden(X30,k1_relat_1(k7_relat_1(X32,X31)))|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.13/0.38  fof(c_0_24, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk1_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk1_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.38  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t95_relat_1])).
% 0.13/0.38  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  fof(c_0_30, plain, ![X18, X19]:((~r1_xboole_0(X18,X19)|k4_xboole_0(X18,X19)=X18)&(k4_xboole_0(X18,X19)!=X18|r1_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.38  cnf(c_0_31, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_32, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_34, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  fof(c_0_35, negated_conjecture, (v1_relat_1(esk3_0)&((k7_relat_1(esk3_0,esk2_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk3_0),esk2_0))&(k7_relat_1(esk3_0,esk2_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk3_0),esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.13/0.38  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|k1_setfam_1(k2_enumset1(X1,X1,X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.13/0.38  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_27]), c_0_28])).
% 0.13/0.38  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_40, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.38  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),X3)|r1_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_43, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_44, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.13/0.38  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(esk3_0,X2))),X2)|r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_48, plain, (r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),k1_relat_1(X2))|r1_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_43, c_0_34])).
% 0.13/0.38  cnf(c_0_49, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_44, c_0_34])).
% 0.13/0.38  cnf(c_0_52, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk3_0,X2)))|~r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(esk3_0,X2))),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_36, c_0_47])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(esk3_0,X2))),k1_relat_1(esk3_0))|r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_48, c_0_42])).
% 0.13/0.38  cnf(c_0_55, plain, (r2_hidden(esk1_2(X1,k1_relat_1(X2)),k1_relat_1(k7_relat_1(X2,X3)))|r1_xboole_0(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(esk1_2(X1,k1_relat_1(X2)),X3)), inference(spm,[status(thm)],[c_0_49, c_0_34])).
% 0.13/0.38  cnf(c_0_56, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_57, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_27]), c_0_28])).
% 0.13/0.38  cnf(c_0_58, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk3_0,X2)))|~r1_xboole_0(k1_relat_1(esk3_0),X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (k7_relat_1(esk3_0,esk2_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_61, plain, (r2_hidden(esk1_2(X1,k1_relat_1(X2)),k1_relat_1(k7_relat_1(X2,X1)))|r1_xboole_0(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.38  cnf(c_0_62, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_38])).
% 0.13/0.38  cnf(c_0_63, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_39, c_0_58])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (k7_relat_1(esk3_0,esk2_0)=k1_xboole_0|r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.38  fof(c_0_65, plain, ![X27, X28]:(~v1_relat_1(X27)|v1_relat_1(k7_relat_1(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (r2_hidden(esk1_2(X1,k1_relat_1(esk3_0)),k1_relat_1(k7_relat_1(esk3_0,X1)))|r1_xboole_0(X1,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_61, c_0_42])).
% 0.13/0.38  fof(c_0_67, plain, ![X29]:((k1_relat_1(X29)!=k1_xboole_0|X29=k1_xboole_0|~v1_relat_1(X29))&(k2_relat_1(X29)!=k1_xboole_0|X29=k1_xboole_0|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.13/0.38  cnf(c_0_68, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_58]), c_0_63])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (k4_xboole_0(X1,k1_relat_1(k7_relat_1(esk3_0,esk2_0)))=X1|k7_relat_1(esk3_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_64])).
% 0.13/0.38  cnf(c_0_70, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (r1_xboole_0(X1,k1_relat_1(esk3_0))|~r2_hidden(esk1_2(X1,k1_relat_1(esk3_0)),X2)|~r1_xboole_0(X2,k1_relat_1(k7_relat_1(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_36, c_0_66])).
% 0.13/0.38  cnf(c_0_72, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,esk2_0))=k1_xboole_0|k7_relat_1(esk3_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_70, c_0_42])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (r1_xboole_0(X1,k1_relat_1(esk3_0))|~r1_xboole_0(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_71, c_0_34])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (k7_relat_1(esk3_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])])).
% 0.13/0.38  cnf(c_0_77, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (k7_relat_1(esk3_0,esk2_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, (r1_xboole_0(esk2_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_58])])).
% 0.13/0.38  cnf(c_0_80, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_76])])).
% 0.13/0.38  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_79]), c_0_80]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 82
% 0.13/0.38  # Proof object clause steps            : 54
% 0.13/0.38  # Proof object formula steps           : 28
% 0.13/0.38  # Proof object conjectures             : 21
% 0.13/0.38  # Proof object clause conjectures      : 18
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 21
% 0.13/0.38  # Proof object initial formulas used   : 14
% 0.13/0.38  # Proof object generating inferences   : 26
% 0.13/0.38  # Proof object simplifying inferences  : 19
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 14
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 24
% 0.13/0.38  # Removed in clause preprocessing      : 3
% 0.13/0.38  # Initial clauses in saturation        : 21
% 0.13/0.38  # Processed clauses                    : 441
% 0.13/0.38  # ...of these trivial                  : 33
% 0.13/0.38  # ...subsumed                          : 170
% 0.13/0.38  # ...remaining for further processing  : 238
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 14
% 0.13/0.38  # Backward-rewritten                   : 54
% 0.13/0.38  # Generated clauses                    : 2097
% 0.13/0.38  # ...of the previous two non-trivial   : 1531
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 2094
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 149
% 0.13/0.38  #    Positive orientable unit clauses  : 34
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 114
% 0.13/0.38  # Current number of unprocessed clauses: 1050
% 0.13/0.38  # ...number of literals in the above   : 1959
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 92
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 4633
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 3841
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 184
% 0.13/0.38  # Unit Clause-clause subsumption calls : 214
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 242
% 0.13/0.38  # BW rewrite match successes           : 19
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 35845
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.062 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.065 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
