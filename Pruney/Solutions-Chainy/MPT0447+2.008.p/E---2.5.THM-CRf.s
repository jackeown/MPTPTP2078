%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:23 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 351 expanded)
%              Number of clauses        :   59 ( 162 expanded)
%              Number of leaves         :   23 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          :  238 ( 700 expanded)
%              Number of equality atoms :   48 ( 208 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(t28_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r2_hidden(X1,k2_relat_1(X2))
          & ! [X3] : ~ r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t15_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(c_0_23,plain,(
    ! [X47,X48] : k1_setfam_1(k2_tarski(X47,X48)) = k3_xboole_0(X47,X48) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X41,X42] : k1_enumset1(X41,X41,X42) = k2_tarski(X41,X42) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k3_xboole_0(X26,X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_32,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_33,plain,(
    ! [X35] : r1_xboole_0(X35,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_34,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_30])).

fof(c_0_36,plain,(
    ! [X28] : r1_tarski(k1_xboole_0,X28) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_42,plain,(
    ! [X50,X51,X52,X54,X55,X56,X57,X59] :
      ( ( ~ r2_hidden(X52,X51)
        | r2_hidden(k4_tarski(X52,esk4_3(X50,X51,X52)),X50)
        | X51 != k1_relat_1(X50) )
      & ( ~ r2_hidden(k4_tarski(X54,X55),X50)
        | r2_hidden(X54,X51)
        | X51 != k1_relat_1(X50) )
      & ( ~ r2_hidden(esk5_2(X56,X57),X57)
        | ~ r2_hidden(k4_tarski(esk5_2(X56,X57),X59),X56)
        | X57 = k1_relat_1(X56) )
      & ( r2_hidden(esk5_2(X56,X57),X57)
        | r2_hidden(k4_tarski(esk5_2(X56,X57),esk6_2(X56,X57)),X56)
        | X57 = k1_relat_1(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_43,plain,(
    ! [X43,X44] : k3_tarski(k2_tarski(X43,X44)) = k2_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_46,plain,(
    ! [X49] :
      ( ~ v1_xboole_0(X49)
      | v1_relat_1(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_47,plain,(
    ! [X38,X39,X40] :
      ( ~ r1_tarski(X38,X39)
      | ~ r1_tarski(X40,X39)
      | r1_tarski(k2_xboole_0(X38,X40),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_48,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_49,plain,(
    ! [X61] :
      ( ~ v1_relat_1(X61)
      | k3_relat_1(X61) = k2_xboole_0(k1_relat_1(X61),k2_relat_1(X61)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_50,plain,(
    ! [X67,X68] :
      ( ~ v1_relat_1(X67)
      | ~ v1_relat_1(X68)
      | r1_tarski(k6_subset_1(k2_relat_1(X67),k2_relat_1(X68)),k2_relat_1(k6_subset_1(X67,X68))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).

fof(c_0_51,plain,(
    ! [X45,X46] : k6_subset_1(X45,X46) = k4_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_52,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_53,plain,(
    ! [X64,X65] :
      ( ~ v1_relat_1(X65)
      | ~ r2_hidden(X64,k2_relat_1(X65))
      | r2_hidden(esk7_2(X64,X65),k1_relat_1(X65)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).

cnf(c_0_54,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_56,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

cnf(c_0_57,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_48,c_0_27])).

cnf(c_0_59,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_60,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | r1_tarski(X19,k2_xboole_0(X21,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_61,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_62,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_65,plain,
    ( r2_hidden(esk7_2(X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_67,plain,(
    ! [X13] :
      ( X13 = k1_xboole_0
      | r2_hidden(esk2_1(X13),X13) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_68,plain,(
    ! [X62,X63] :
      ( ~ v1_relat_1(X62)
      | ~ v1_relat_1(X63)
      | r1_tarski(k6_subset_1(k1_relat_1(X62),k1_relat_1(X63)),k1_relat_1(k6_subset_1(X62,X63))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).

fof(c_0_69,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_relat_1(esk9_0)
    & r1_tarski(esk8_0,esk9_0)
    & ~ r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).

cnf(c_0_70,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_71,plain,
    ( k3_relat_1(X1) = k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_59,c_0_58])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_63])).

fof(c_0_75,plain,(
    ! [X17,X18] :
      ( ( k4_xboole_0(X17,X18) != k1_xboole_0
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | k4_xboole_0(X17,X18) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_78,plain,(
    ! [X32,X33,X34] :
      ( ~ r1_tarski(k4_xboole_0(X32,X33),X34)
      | r1_tarski(X32,k2_xboole_0(X33,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_79,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_58])).

cnf(c_0_84,plain,
    ( k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) = k2_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_86,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_88,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_63]),c_0_63])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk8_0),k3_relat_1(esk9_0))
    | ~ r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_71])).

cnf(c_0_91,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_93,plain,
    ( k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_86]),c_0_40])])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_87,c_0_58])).

cnf(c_0_95,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_88])).

cnf(c_0_96,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_77])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk9_0))
    | ~ r1_tarski(k2_relat_1(esk8_0),k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])])).

cnf(c_0_98,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_100,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_71])).

cnf(c_0_101,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_85]),c_0_96]),c_0_96]),c_0_40])])).

cnf(c_0_102,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_91]),c_0_82]),c_0_99])])).

cnf(c_0_103,plain,
    ( r1_tarski(k1_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_40])])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_91]),c_0_82]),c_0_99])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.43/0.59  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.43/0.59  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.43/0.59  #
% 0.43/0.59  # Preprocessing time       : 0.025 s
% 0.43/0.59  
% 0.43/0.59  # Proof found!
% 0.43/0.59  # SZS status Theorem
% 0.43/0.59  # SZS output start CNFRefutation
% 0.43/0.59  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.43/0.59  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.43/0.59  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.43/0.59  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.43/0.59  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.43/0.59  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.43/0.59  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.43/0.59  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.43/0.59  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.43/0.59  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.43/0.59  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.43/0.59  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.43/0.59  fof(t28_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 0.43/0.59  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.43/0.59  fof(t19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~((r2_hidden(X1,k2_relat_1(X2))&![X3]:~(r2_hidden(X3,k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 0.43/0.59  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.43/0.59  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 0.43/0.59  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.43/0.59  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.43/0.59  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.43/0.59  fof(t15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 0.43/0.59  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.43/0.59  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.43/0.59  fof(c_0_23, plain, ![X47, X48]:k1_setfam_1(k2_tarski(X47,X48))=k3_xboole_0(X47,X48), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.43/0.59  fof(c_0_24, plain, ![X41, X42]:k1_enumset1(X41,X41,X42)=k2_tarski(X41,X42), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.43/0.59  fof(c_0_25, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.43/0.59  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.43/0.59  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.43/0.59  fof(c_0_28, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k3_xboole_0(X26,X27)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.43/0.59  cnf(c_0_29, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.43/0.59  cnf(c_0_30, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.43/0.59  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.43/0.59  fof(c_0_32, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.43/0.59  fof(c_0_33, plain, ![X35]:r1_xboole_0(X35,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.43/0.59  cnf(c_0_34, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.43/0.59  cnf(c_0_35, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_30])).
% 0.43/0.59  fof(c_0_36, plain, ![X28]:r1_tarski(k1_xboole_0,X28), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.43/0.59  cnf(c_0_37, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.43/0.59  cnf(c_0_38, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.43/0.59  cnf(c_0_39, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.43/0.59  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.43/0.59  cnf(c_0_41, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.43/0.59  fof(c_0_42, plain, ![X50, X51, X52, X54, X55, X56, X57, X59]:(((~r2_hidden(X52,X51)|r2_hidden(k4_tarski(X52,esk4_3(X50,X51,X52)),X50)|X51!=k1_relat_1(X50))&(~r2_hidden(k4_tarski(X54,X55),X50)|r2_hidden(X54,X51)|X51!=k1_relat_1(X50)))&((~r2_hidden(esk5_2(X56,X57),X57)|~r2_hidden(k4_tarski(esk5_2(X56,X57),X59),X56)|X57=k1_relat_1(X56))&(r2_hidden(esk5_2(X56,X57),X57)|r2_hidden(k4_tarski(esk5_2(X56,X57),esk6_2(X56,X57)),X56)|X57=k1_relat_1(X56)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.43/0.59  fof(c_0_43, plain, ![X43, X44]:k3_tarski(k2_tarski(X43,X44))=k2_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.43/0.59  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.43/0.59  cnf(c_0_45, plain, (r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.43/0.59  fof(c_0_46, plain, ![X49]:(~v1_xboole_0(X49)|v1_relat_1(X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.43/0.59  fof(c_0_47, plain, ![X38, X39, X40]:(~r1_tarski(X38,X39)|~r1_tarski(X40,X39)|r1_tarski(k2_xboole_0(X38,X40),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.43/0.59  cnf(c_0_48, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.43/0.59  fof(c_0_49, plain, ![X61]:(~v1_relat_1(X61)|k3_relat_1(X61)=k2_xboole_0(k1_relat_1(X61),k2_relat_1(X61))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.43/0.59  fof(c_0_50, plain, ![X67, X68]:(~v1_relat_1(X67)|(~v1_relat_1(X68)|r1_tarski(k6_subset_1(k2_relat_1(X67),k2_relat_1(X68)),k2_relat_1(k6_subset_1(X67,X68))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).
% 0.43/0.59  fof(c_0_51, plain, ![X45, X46]:k6_subset_1(X45,X46)=k4_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.43/0.59  cnf(c_0_52, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.43/0.59  fof(c_0_53, plain, ![X64, X65]:(~v1_relat_1(X65)|(~r2_hidden(X64,k2_relat_1(X65))|r2_hidden(esk7_2(X64,X65),k1_relat_1(X65)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).
% 0.43/0.59  cnf(c_0_54, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.43/0.59  cnf(c_0_55, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.43/0.59  fof(c_0_56, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 0.43/0.59  cnf(c_0_57, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.43/0.59  cnf(c_0_58, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_48, c_0_27])).
% 0.43/0.59  cnf(c_0_59, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.43/0.59  fof(c_0_60, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|r1_tarski(X19,k2_xboole_0(X21,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.43/0.59  fof(c_0_61, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.43/0.59  cnf(c_0_62, plain, (r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.43/0.59  cnf(c_0_63, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.43/0.59  cnf(c_0_64, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_52])).
% 0.43/0.59  cnf(c_0_65, plain, (r2_hidden(esk7_2(X2,X1),k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.43/0.59  cnf(c_0_66, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.43/0.59  fof(c_0_67, plain, ![X13]:(X13=k1_xboole_0|r2_hidden(esk2_1(X13),X13)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.43/0.59  fof(c_0_68, plain, ![X62, X63]:(~v1_relat_1(X62)|(~v1_relat_1(X63)|r1_tarski(k6_subset_1(k1_relat_1(X62),k1_relat_1(X63)),k1_relat_1(k6_subset_1(X62,X63))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).
% 0.43/0.59  fof(c_0_69, negated_conjecture, (v1_relat_1(esk8_0)&(v1_relat_1(esk9_0)&(r1_tarski(esk8_0,esk9_0)&~r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).
% 0.43/0.59  cnf(c_0_70, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.43/0.59  cnf(c_0_71, plain, (k3_relat_1(X1)=k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_59, c_0_58])).
% 0.43/0.59  cnf(c_0_72, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.43/0.59  cnf(c_0_73, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.43/0.59  cnf(c_0_74, plain, (r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_63])).
% 0.43/0.59  fof(c_0_75, plain, ![X17, X18]:((k4_xboole_0(X17,X18)!=k1_xboole_0|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|k4_xboole_0(X17,X18)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.43/0.59  cnf(c_0_76, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 0.43/0.59  cnf(c_0_77, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.43/0.59  fof(c_0_78, plain, ![X32, X33, X34]:(~r1_tarski(k4_xboole_0(X32,X33),X34)|r1_tarski(X32,k2_xboole_0(X33,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.43/0.59  cnf(c_0_79, plain, (r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.43/0.59  cnf(c_0_80, negated_conjecture, (~r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.43/0.59  cnf(c_0_81, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.43/0.59  cnf(c_0_82, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.43/0.59  cnf(c_0_83, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_58])).
% 0.43/0.59  cnf(c_0_84, plain, (k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=k2_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.43/0.59  cnf(c_0_85, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.43/0.59  cnf(c_0_86, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.43/0.59  cnf(c_0_87, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.43/0.59  cnf(c_0_88, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_63]), c_0_63])).
% 0.43/0.59  cnf(c_0_89, negated_conjecture, (~r1_tarski(k2_relat_1(esk8_0),k3_relat_1(esk9_0))|~r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])])).
% 0.43/0.59  cnf(c_0_90, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_83, c_0_71])).
% 0.43/0.59  cnf(c_0_91, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.43/0.59  cnf(c_0_92, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.43/0.59  cnf(c_0_93, plain, (k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_86]), c_0_40])])).
% 0.43/0.59  cnf(c_0_94, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_87, c_0_58])).
% 0.43/0.59  cnf(c_0_95, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_73, c_0_88])).
% 0.43/0.59  cnf(c_0_96, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_77])).
% 0.43/0.59  cnf(c_0_97, negated_conjecture, (~r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk9_0))|~r1_tarski(k2_relat_1(esk8_0),k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])])).
% 0.43/0.59  cnf(c_0_98, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.43/0.59  cnf(c_0_99, negated_conjecture, (r1_tarski(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.43/0.59  cnf(c_0_100, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_94, c_0_71])).
% 0.43/0.59  cnf(c_0_101, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_85]), c_0_96]), c_0_96]), c_0_40])])).
% 0.43/0.59  cnf(c_0_102, negated_conjecture, (~r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_91]), c_0_82]), c_0_99])])).
% 0.43/0.59  cnf(c_0_103, plain, (r1_tarski(k1_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_40])])).
% 0.43/0.59  cnf(c_0_104, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_91]), c_0_82]), c_0_99])]), ['proof']).
% 0.43/0.59  # SZS output end CNFRefutation
% 0.43/0.59  # Proof object total steps             : 105
% 0.43/0.59  # Proof object clause steps            : 59
% 0.43/0.59  # Proof object formula steps           : 46
% 0.43/0.59  # Proof object conjectures             : 11
% 0.43/0.59  # Proof object clause conjectures      : 8
% 0.43/0.59  # Proof object formula conjectures     : 3
% 0.43/0.59  # Proof object initial clauses used    : 27
% 0.43/0.59  # Proof object initial formulas used   : 23
% 0.43/0.59  # Proof object generating inferences   : 22
% 0.43/0.59  # Proof object simplifying inferences  : 38
% 0.43/0.59  # Training examples: 0 positive, 0 negative
% 0.43/0.59  # Parsed axioms                        : 26
% 0.43/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.43/0.59  # Initial clauses                      : 38
% 0.43/0.59  # Removed in clause preprocessing      : 4
% 0.43/0.59  # Initial clauses in saturation        : 34
% 0.43/0.59  # Processed clauses                    : 1723
% 0.43/0.59  # ...of these trivial                  : 3
% 0.43/0.59  # ...subsumed                          : 1033
% 0.43/0.59  # ...remaining for further processing  : 687
% 0.43/0.59  # Other redundant clauses eliminated   : 2
% 0.43/0.59  # Clauses deleted for lack of memory   : 0
% 0.43/0.59  # Backward-subsumed                    : 60
% 0.43/0.59  # Backward-rewritten                   : 23
% 0.43/0.59  # Generated clauses                    : 11400
% 0.43/0.59  # ...of the previous two non-trivial   : 9950
% 0.43/0.59  # Contextual simplify-reflections      : 5
% 0.43/0.59  # Paramodulations                      : 11361
% 0.43/0.59  # Factorizations                       : 10
% 0.43/0.59  # Equation resolutions                 : 29
% 0.43/0.59  # Propositional unsat checks           : 0
% 0.43/0.59  #    Propositional check models        : 0
% 0.43/0.59  #    Propositional check unsatisfiable : 0
% 0.43/0.59  #    Propositional clauses             : 0
% 0.43/0.59  #    Propositional clauses after purity: 0
% 0.43/0.59  #    Propositional unsat core size     : 0
% 0.43/0.59  #    Propositional preprocessing time  : 0.000
% 0.43/0.59  #    Propositional encoding time       : 0.000
% 0.43/0.59  #    Propositional solver time         : 0.000
% 0.43/0.59  #    Success case prop preproc time    : 0.000
% 0.43/0.59  #    Success case prop encoding time   : 0.000
% 0.43/0.59  #    Success case prop solver time     : 0.000
% 0.43/0.59  # Current number of processed clauses  : 602
% 0.43/0.59  #    Positive orientable unit clauses  : 23
% 0.43/0.59  #    Positive unorientable unit clauses: 0
% 0.43/0.59  #    Negative unit clauses             : 11
% 0.43/0.59  #    Non-unit-clauses                  : 568
% 0.43/0.59  # Current number of unprocessed clauses: 8031
% 0.43/0.59  # ...number of literals in the above   : 31762
% 0.43/0.59  # Current number of archived formulas  : 0
% 0.43/0.59  # Current number of archived clauses   : 87
% 0.43/0.59  # Clause-clause subsumption calls (NU) : 68323
% 0.43/0.59  # Rec. Clause-clause subsumption calls : 27095
% 0.43/0.59  # Non-unit clause-clause subsumptions  : 857
% 0.43/0.59  # Unit Clause-clause subsumption calls : 2613
% 0.43/0.59  # Rewrite failures with RHS unbound    : 0
% 0.43/0.59  # BW rewrite match attempts            : 90
% 0.43/0.59  # BW rewrite match successes           : 12
% 0.43/0.59  # Condensation attempts                : 0
% 0.43/0.59  # Condensation successes               : 0
% 0.43/0.59  # Termbank termtop insertions          : 205532
% 0.43/0.60  
% 0.43/0.60  # -------------------------------------------------
% 0.43/0.60  # User time                : 0.250 s
% 0.43/0.60  # System time              : 0.009 s
% 0.43/0.60  # Total time               : 0.259 s
% 0.43/0.60  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
