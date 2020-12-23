%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:32 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 128 expanded)
%              Number of clauses        :   36 (  56 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 ( 255 expanded)
%              Number of equality atoms :   63 ( 108 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t110_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(t213_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1))) = k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t212_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

fof(c_0_17,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X43)
      | v1_relat_1(k7_relat_1(X43,X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_18,plain,(
    ! [X45] :
      ( ~ v1_relat_1(X45)
      | k7_relat_1(X45,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1))) = k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) ) ),
    inference(assume_negation,[status(cth)],[t213_relat_1])).

fof(c_0_20,plain,(
    ! [X30] : k2_xboole_0(X30,k1_xboole_0) = X30 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_21,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k2_xboole_0(X28,X29) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_22,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & k6_subset_1(k1_relat_1(esk6_0),k1_relat_1(k7_relat_1(esk6_0,esk5_0))) != k1_relat_1(k6_subset_1(esk6_0,k7_relat_1(esk6_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X52)
      | r1_tarski(k7_relat_1(X52,X51),X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_28,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( r2_hidden(X19,X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | ~ r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X22)
        | X23 = k4_xboole_0(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X22)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_31,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_32,plain,(
    ! [X53,X54] :
      ( ~ v1_relat_1(X54)
      | k1_relat_1(k7_relat_1(X54,X53)) = k3_xboole_0(k1_relat_1(X54),X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_33,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X33] : k4_xboole_0(k1_xboole_0,X33) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_41,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X31,X32] : k4_xboole_0(k2_xboole_0(X31,X32),X32) = k4_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_41]),c_0_35])])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_48,plain,(
    ! [X36,X37,X38,X39,X40] :
      ( ( ~ r1_tarski(X36,X37)
        | ~ r2_hidden(k4_tarski(X38,X39),X36)
        | r2_hidden(k4_tarski(X38,X39),X37)
        | ~ v1_relat_1(X36) )
      & ( r2_hidden(k4_tarski(esk3_2(X36,X40),esk4_2(X36,X40)),X36)
        | r1_tarski(X36,X40)
        | ~ v1_relat_1(X36) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X36,X40),esk4_2(X36,X40)),X40)
        | r1_tarski(X36,X40)
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_49,plain,(
    ! [X34,X35] : k6_subset_1(X34,X35) = k4_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_52,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k6_subset_1(k1_relat_1(esk6_0),k1_relat_1(k7_relat_1(esk6_0,esk5_0))) != k1_relat_1(k6_subset_1(esk6_0,k7_relat_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_54,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_55,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_56,plain,(
    ! [X25,X26,X27] : k4_xboole_0(X25,k3_xboole_0(X26,X27)) = k2_xboole_0(k4_xboole_0(X25,X26),k4_xboole_0(X25,X27)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_26])).

cnf(c_0_58,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_35])])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk6_0),k1_relat_1(k7_relat_1(esk6_0,esk5_0))) != k1_relat_1(k4_xboole_0(esk6_0,k7_relat_1(esk6_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_54])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_43])).

fof(c_0_63,plain,(
    ! [X49,X50] :
      ( ~ v1_relat_1(X50)
      | k1_relat_1(k6_subset_1(X50,k7_relat_1(X50,X49))) = k6_subset_1(k1_relat_1(X50),X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t212_relat_1])])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk6_0),k3_xboole_0(esk5_0,k1_relat_1(esk6_0))) != k1_relat_1(k4_xboole_0(esk6_0,k7_relat_1(esk6_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_39]),c_0_29])]),c_0_60])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_25])).

cnf(c_0_66,plain,
    ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X2))) = k6_subset_1(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(k4_xboole_0(esk6_0,k7_relat_1(esk6_0,esk5_0))) != k4_xboole_0(k1_relat_1(esk6_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,plain,
    ( k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2))) = k4_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_54]),c_0_54])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.18/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.028 s
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.18/0.38  fof(t110_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 0.18/0.38  fof(t213_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1)))=k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 0.18/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.18/0.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.18/0.38  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.18/0.38  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.18/0.38  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.18/0.38  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.18/0.38  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.18/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.18/0.38  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.18/0.38  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.18/0.38  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.18/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.38  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 0.18/0.38  fof(t212_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))=k6_subset_1(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 0.18/0.38  fof(c_0_17, plain, ![X43, X44]:(~v1_relat_1(X43)|v1_relat_1(k7_relat_1(X43,X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.18/0.38  fof(c_0_18, plain, ![X45]:(~v1_relat_1(X45)|k7_relat_1(X45,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).
% 0.18/0.38  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1)))=k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))))), inference(assume_negation,[status(cth)],[t213_relat_1])).
% 0.18/0.38  fof(c_0_20, plain, ![X30]:k2_xboole_0(X30,k1_xboole_0)=X30, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.18/0.38  fof(c_0_21, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k2_xboole_0(X28,X29)=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.18/0.38  cnf(c_0_22, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_23, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.38  fof(c_0_24, negated_conjecture, (v1_relat_1(esk6_0)&k6_subset_1(k1_relat_1(esk6_0),k1_relat_1(k7_relat_1(esk6_0,esk5_0)))!=k1_relat_1(k6_subset_1(esk6_0,k7_relat_1(esk6_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.18/0.38  cnf(c_0_25, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.38  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.38  fof(c_0_27, plain, ![X51, X52]:(~v1_relat_1(X52)|r1_tarski(k7_relat_1(X52,X51),X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.18/0.38  cnf(c_0_28, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.38  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.38  fof(c_0_30, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk2_3(X21,X22,X23),X23)|(~r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk2_3(X21,X22,X23),X22)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.18/0.38  fof(c_0_31, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.18/0.38  fof(c_0_32, plain, ![X53, X54]:(~v1_relat_1(X54)|k1_relat_1(k7_relat_1(X54,X53))=k3_xboole_0(k1_relat_1(X54),X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.18/0.38  cnf(c_0_33, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.38  cnf(c_0_34, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.38  cnf(c_0_35, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.38  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.38  fof(c_0_37, plain, ![X33]:k4_xboole_0(k1_xboole_0,X33)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.18/0.38  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.38  cnf(c_0_39, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.38  cnf(c_0_40, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.18/0.38  cnf(c_0_41, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.18/0.38  cnf(c_0_42, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_36])).
% 0.18/0.38  cnf(c_0_43, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.38  fof(c_0_44, plain, ![X31, X32]:k4_xboole_0(k2_xboole_0(X31,X32),X32)=k4_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.18/0.38  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_38])).
% 0.18/0.38  cnf(c_0_46, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_41]), c_0_35])])).
% 0.18/0.38  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.38  fof(c_0_48, plain, ![X36, X37, X38, X39, X40]:((~r1_tarski(X36,X37)|(~r2_hidden(k4_tarski(X38,X39),X36)|r2_hidden(k4_tarski(X38,X39),X37))|~v1_relat_1(X36))&((r2_hidden(k4_tarski(esk3_2(X36,X40),esk4_2(X36,X40)),X36)|r1_tarski(X36,X40)|~v1_relat_1(X36))&(~r2_hidden(k4_tarski(esk3_2(X36,X40),esk4_2(X36,X40)),X40)|r1_tarski(X36,X40)|~v1_relat_1(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.18/0.38  fof(c_0_49, plain, ![X34, X35]:k6_subset_1(X34,X35)=k4_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.18/0.38  cnf(c_0_50, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.38  cnf(c_0_51, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.18/0.38  cnf(c_0_52, plain, (r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.38  cnf(c_0_53, negated_conjecture, (k6_subset_1(k1_relat_1(esk6_0),k1_relat_1(k7_relat_1(esk6_0,esk5_0)))!=k1_relat_1(k6_subset_1(esk6_0,k7_relat_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.38  cnf(c_0_54, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.18/0.38  fof(c_0_55, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.38  fof(c_0_56, plain, ![X25, X26, X27]:k4_xboole_0(X25,k3_xboole_0(X26,X27))=k2_xboole_0(k4_xboole_0(X25,X26),k4_xboole_0(X25,X27)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 0.18/0.38  cnf(c_0_57, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(X2,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_50, c_0_26])).
% 0.18/0.38  cnf(c_0_58, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_35])])).
% 0.18/0.38  cnf(c_0_59, negated_conjecture, (k4_xboole_0(k1_relat_1(esk6_0),k1_relat_1(k7_relat_1(esk6_0,esk5_0)))!=k1_relat_1(k4_xboole_0(esk6_0,k7_relat_1(esk6_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_54])).
% 0.18/0.38  cnf(c_0_60, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.18/0.38  cnf(c_0_61, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.18/0.38  cnf(c_0_62, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_43])).
% 0.18/0.38  fof(c_0_63, plain, ![X49, X50]:(~v1_relat_1(X50)|k1_relat_1(k6_subset_1(X50,k7_relat_1(X50,X49)))=k6_subset_1(k1_relat_1(X50),X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t212_relat_1])])).
% 0.18/0.38  cnf(c_0_64, negated_conjecture, (k4_xboole_0(k1_relat_1(esk6_0),k3_xboole_0(esk5_0,k1_relat_1(esk6_0)))!=k1_relat_1(k4_xboole_0(esk6_0,k7_relat_1(esk6_0,esk5_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_39]), c_0_29])]), c_0_60])).
% 0.18/0.38  cnf(c_0_65, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_25])).
% 0.18/0.38  cnf(c_0_66, plain, (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X2)))=k6_subset_1(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.38  cnf(c_0_67, negated_conjecture, (k1_relat_1(k4_xboole_0(esk6_0,k7_relat_1(esk6_0,esk5_0)))!=k4_xboole_0(k1_relat_1(esk6_0),esk5_0)), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.18/0.38  cnf(c_0_68, plain, (k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2)))=k4_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_54]), c_0_54])).
% 0.18/0.38  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_29])]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 70
% 0.18/0.38  # Proof object clause steps            : 36
% 0.18/0.38  # Proof object formula steps           : 34
% 0.18/0.38  # Proof object conjectures             : 10
% 0.18/0.38  # Proof object clause conjectures      : 7
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 18
% 0.18/0.38  # Proof object initial formulas used   : 17
% 0.18/0.38  # Proof object generating inferences   : 13
% 0.18/0.38  # Proof object simplifying inferences  : 23
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 19
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 33
% 0.18/0.38  # Removed in clause preprocessing      : 1
% 0.18/0.38  # Initial clauses in saturation        : 32
% 0.18/0.38  # Processed clauses                    : 173
% 0.18/0.38  # ...of these trivial                  : 26
% 0.18/0.38  # ...subsumed                          : 61
% 0.18/0.38  # ...remaining for further processing  : 86
% 0.18/0.38  # Other redundant clauses eliminated   : 6
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 2
% 0.18/0.38  # Backward-rewritten                   : 17
% 0.18/0.38  # Generated clauses                    : 758
% 0.18/0.38  # ...of the previous two non-trivial   : 436
% 0.18/0.38  # Contextual simplify-reflections      : 1
% 0.18/0.38  # Paramodulations                      : 752
% 0.18/0.38  # Factorizations                       : 0
% 0.18/0.38  # Equation resolutions                 : 6
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
% 0.18/0.38  # Current number of processed clauses  : 61
% 0.18/0.38  #    Positive orientable unit clauses  : 26
% 0.18/0.38  #    Positive unorientable unit clauses: 1
% 0.18/0.38  #    Negative unit clauses             : 3
% 0.18/0.38  #    Non-unit-clauses                  : 31
% 0.18/0.38  # Current number of unprocessed clauses: 288
% 0.18/0.38  # ...number of literals in the above   : 523
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 20
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 473
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 420
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 26
% 0.18/0.38  # Unit Clause-clause subsumption calls : 17
% 0.18/0.38  # Rewrite failures with RHS unbound    : 26
% 0.18/0.38  # BW rewrite match attempts            : 87
% 0.18/0.38  # BW rewrite match successes           : 25
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 10548
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.038 s
% 0.18/0.38  # System time              : 0.004 s
% 0.18/0.38  # Total time               : 0.042 s
% 0.18/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
