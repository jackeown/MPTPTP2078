%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:35 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 201 expanded)
%              Number of clauses        :   38 (  82 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  141 ( 343 expanded)
%              Number of equality atoms :   49 ( 167 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t67_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))
           => k5_relat_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t75_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(t95_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc10_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_19,plain,(
    ! [X49,X50] : k1_setfam_1(k2_tarski(X49,X50)) = k3_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X56,X57] :
      ( ~ v1_relat_1(X57)
      | k1_relat_1(k7_relat_1(X57,X56)) = k3_xboole_0(k1_relat_1(X57),X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X27,X28,X29,X30] : k3_enumset1(X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X31,X32,X33,X34,X35] : k4_enumset1(X31,X31,X32,X33,X34,X35) = k3_enumset1(X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_27,plain,(
    ! [X36,X37,X38,X39,X40,X41] : k5_enumset1(X36,X36,X37,X38,X39,X40,X41) = k4_enumset1(X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_28,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48] : k6_enumset1(X42,X42,X43,X44,X45,X46,X47,X48) = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_29,plain,(
    ! [X53,X54] :
      ( ~ v1_relat_1(X53)
      | ~ v1_relat_1(X54)
      | ~ r1_xboole_0(k2_relat_1(X53),k1_relat_1(X54))
      | k5_relat_1(X53,X54) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_relat_1])])])).

fof(c_0_30,plain,(
    ! [X55] :
      ( k1_relat_1(k6_relat_1(X55)) = X55
      & k2_relat_1(k6_relat_1(X55)) = X55 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_31,plain,(
    ! [X51] : v1_relat_1(k6_relat_1(X51)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_32,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_33,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_34,plain,(
    ! [X20,X21] :
      ( r1_xboole_0(X20,X21)
      | ~ r1_xboole_0(k3_xboole_0(X20,X21),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).

cnf(c_0_35,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k7_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t95_relat_1])).

fof(c_0_43,plain,(
    ! [X58,X59] :
      ( ~ v1_relat_1(X59)
      | k7_relat_1(X59,X58) = k5_relat_1(k6_relat_1(X58),X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_44,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_49,plain,(
    ! [X52] :
      ( ~ v1_xboole_0(X52)
      | v1_xboole_0(k1_relat_1(X52)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_52,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_53,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( k7_relat_1(esk4_0,esk3_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) )
    & ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

cnf(c_0_54,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( k5_relat_1(k6_relat_1(X1),X2) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(X1,k1_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

fof(c_0_56,plain,(
    ! [X12,X13] :
      ( ~ r1_xboole_0(X12,X13)
      | r1_xboole_0(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_60,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_46])])).

cnf(c_0_61,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,k1_relat_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X1)),X2)) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_51,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])]),c_0_64])).

cnf(c_0_71,plain,
    ( r1_xboole_0(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_63]),c_0_74])]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:17:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.18/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.027 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.18/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.38  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.18/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.18/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.18/0.38  fof(t67_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))=>k5_relat_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_relat_1)).
% 0.18/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.18/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.18/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.18/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.18/0.38  fof(t75_xboole_1, axiom, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.18/0.38  fof(t95_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 0.18/0.38  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.18/0.38  fof(fc10_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k1_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 0.18/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.18/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.38  fof(c_0_19, plain, ![X49, X50]:k1_setfam_1(k2_tarski(X49,X50))=k3_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.18/0.38  fof(c_0_20, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.38  fof(c_0_21, plain, ![X56, X57]:(~v1_relat_1(X57)|k1_relat_1(k7_relat_1(X57,X56))=k3_xboole_0(k1_relat_1(X57),X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.18/0.38  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.38  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.38  fof(c_0_24, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.38  fof(c_0_25, plain, ![X27, X28, X29, X30]:k3_enumset1(X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.38  fof(c_0_26, plain, ![X31, X32, X33, X34, X35]:k4_enumset1(X31,X31,X32,X33,X34,X35)=k3_enumset1(X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.18/0.38  fof(c_0_27, plain, ![X36, X37, X38, X39, X40, X41]:k5_enumset1(X36,X36,X37,X38,X39,X40,X41)=k4_enumset1(X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.18/0.38  fof(c_0_28, plain, ![X42, X43, X44, X45, X46, X47, X48]:k6_enumset1(X42,X42,X43,X44,X45,X46,X47,X48)=k5_enumset1(X42,X43,X44,X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.18/0.38  fof(c_0_29, plain, ![X53, X54]:(~v1_relat_1(X53)|(~v1_relat_1(X54)|(~r1_xboole_0(k2_relat_1(X53),k1_relat_1(X54))|k5_relat_1(X53,X54)=k1_xboole_0))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_relat_1])])])).
% 0.18/0.38  fof(c_0_30, plain, ![X55]:(k1_relat_1(k6_relat_1(X55))=X55&k2_relat_1(k6_relat_1(X55))=X55), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.18/0.38  fof(c_0_31, plain, ![X51]:v1_relat_1(k6_relat_1(X51)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.18/0.38  fof(c_0_32, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.18/0.38  fof(c_0_33, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk2_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk2_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.18/0.38  fof(c_0_34, plain, ![X20, X21]:(r1_xboole_0(X20,X21)|~r1_xboole_0(k3_xboole_0(X20,X21),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).
% 0.18/0.38  cnf(c_0_35, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.38  cnf(c_0_36, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.38  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.38  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.38  cnf(c_0_39, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.38  cnf(c_0_40, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.38  cnf(c_0_41, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.38  fof(c_0_42, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t95_relat_1])).
% 0.18/0.38  fof(c_0_43, plain, ![X58, X59]:(~v1_relat_1(X59)|k7_relat_1(X59,X58)=k5_relat_1(k6_relat_1(X58),X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.18/0.38  cnf(c_0_44, plain, (k5_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.38  cnf(c_0_45, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.38  cnf(c_0_46, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.38  cnf(c_0_47, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.38  cnf(c_0_48, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.38  fof(c_0_49, plain, ![X52]:(~v1_xboole_0(X52)|v1_xboole_0(k1_relat_1(X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).
% 0.18/0.38  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k3_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.38  cnf(c_0_51, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.18/0.38  cnf(c_0_52, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.38  fof(c_0_53, negated_conjecture, (v1_relat_1(esk4_0)&((k7_relat_1(esk4_0,esk3_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk4_0),esk3_0))&(k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk4_0),esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 0.18/0.38  cnf(c_0_54, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.38  cnf(c_0_55, plain, (k5_relat_1(k6_relat_1(X1),X2)=k1_xboole_0|~v1_relat_1(X2)|~r1_xboole_0(X1,k1_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.18/0.38  fof(c_0_56, plain, ![X12, X13]:(~r1_xboole_0(X12,X13)|r1_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.18/0.38  cnf(c_0_57, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.18/0.38  cnf(c_0_58, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.18/0.38  cnf(c_0_59, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.18/0.38  cnf(c_0_60, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_46])])).
% 0.18/0.38  cnf(c_0_61, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.38  cnf(c_0_62, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.18/0.38  cnf(c_0_63, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.38  cnf(c_0_64, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.18/0.38  cnf(c_0_65, plain, (r1_xboole_0(X1,k1_relat_1(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.18/0.38  cnf(c_0_66, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.38  cnf(c_0_67, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.18/0.38  cnf(c_0_68, plain, (k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X1)),X2))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_51, c_0_60])).
% 0.18/0.38  cnf(c_0_69, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.38  cnf(c_0_70, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])]), c_0_64])).
% 0.18/0.38  cnf(c_0_71, plain, (r1_xboole_0(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.18/0.38  cnf(c_0_72, plain, (r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.18/0.38  cnf(c_0_73, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_69, c_0_70])).
% 0.18/0.38  cnf(c_0_74, plain, (r1_xboole_0(k1_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_64, c_0_71])).
% 0.18/0.38  cnf(c_0_75, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_63]), c_0_74])]), c_0_70]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 76
% 0.18/0.38  # Proof object clause steps            : 38
% 0.18/0.38  # Proof object formula steps           : 38
% 0.18/0.38  # Proof object conjectures             : 9
% 0.18/0.38  # Proof object clause conjectures      : 6
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 22
% 0.18/0.38  # Proof object initial formulas used   : 19
% 0.18/0.38  # Proof object generating inferences   : 10
% 0.18/0.38  # Proof object simplifying inferences  : 27
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 19
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 25
% 0.18/0.38  # Removed in clause preprocessing      : 7
% 0.18/0.38  # Initial clauses in saturation        : 18
% 0.18/0.38  # Processed clauses                    : 269
% 0.18/0.38  # ...of these trivial                  : 11
% 0.18/0.38  # ...subsumed                          : 61
% 0.18/0.38  # ...remaining for further processing  : 197
% 0.18/0.38  # Other redundant clauses eliminated   : 0
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 5
% 0.18/0.38  # Backward-rewritten                   : 13
% 0.18/0.38  # Generated clauses                    : 631
% 0.18/0.38  # ...of the previous two non-trivial   : 412
% 0.18/0.38  # Contextual simplify-reflections      : 1
% 0.18/0.38  # Paramodulations                      : 630
% 0.18/0.38  # Factorizations                       : 0
% 0.18/0.38  # Equation resolutions                 : 0
% 0.18/0.38  # Propositional unsat checks           : 0
% 0.18/0.38  #    Propositional check models        : 0
% 0.18/0.38  #    Propositional check unsatisfiable : 0
% 0.18/0.38  #    Propositional clauses             : 0
% 0.18/0.38  #    Propositional clauses after purity: 0
% 0.18/0.38  #    Propositional unsat core size     : 0
% 0.18/0.38  #    Propositional preprocessing time  : 0.000
% 0.18/0.38  #    Propositional encoding time       : 0.000
% 0.18/0.38  #    Propositional solver time         : 0.000
% 0.18/0.38  #    Success case prop preproc time    : 0.000
% 0.18/0.38  #    Success case prop encoding time   : 0.000
% 0.18/0.38  #    Success case prop solver time     : 0.000
% 0.18/0.38  # Current number of processed clauses  : 160
% 0.18/0.38  #    Positive orientable unit clauses  : 41
% 0.18/0.38  #    Positive unorientable unit clauses: 0
% 0.18/0.38  #    Negative unit clauses             : 1
% 0.18/0.38  #    Non-unit-clauses                  : 118
% 0.18/0.38  # Current number of unprocessed clauses: 167
% 0.18/0.38  # ...number of literals in the above   : 666
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 44
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 2875
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 1536
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 66
% 0.18/0.38  # Unit Clause-clause subsumption calls : 5
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 182
% 0.18/0.38  # BW rewrite match successes           : 13
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 14979
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.042 s
% 0.18/0.38  # System time              : 0.006 s
% 0.18/0.38  # Total time               : 0.048 s
% 0.18/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
