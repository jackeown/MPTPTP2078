%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:27 EST 2020

% Result     : Theorem 1.29s
% Output     : CNFRefutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 531 expanded)
%              Number of clauses        :   61 ( 244 expanded)
%              Number of leaves         :   23 ( 139 expanded)
%              Depth                    :   18
%              Number of atoms          :  251 (1002 expanded)
%              Number of equality atoms :   67 ( 412 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

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

fof(t15_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

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

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t28_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_23,plain,(
    ! [X52,X53] : k1_setfam_1(k2_tarski(X52,X53)) = k3_xboole_0(X52,X53) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X45,X46,X47] : k2_enumset1(X45,X45,X46,X47) = k1_enumset1(X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X34,X35] : k4_xboole_0(X34,k4_xboole_0(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X27] :
      ( ~ r1_tarski(X27,k1_xboole_0)
      | X27 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_35,plain,(
    ! [X25,X26] : r1_tarski(k4_xboole_0(X25,X26),X25) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_36,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_42,plain,(
    ! [X65,X66,X67,X69,X70,X71,X72,X74] :
      ( ( ~ r2_hidden(X67,X66)
        | r2_hidden(k4_tarski(esk6_3(X65,X66,X67),X67),X65)
        | X66 != k2_relat_1(X65) )
      & ( ~ r2_hidden(k4_tarski(X70,X69),X65)
        | r2_hidden(X69,X66)
        | X66 != k2_relat_1(X65) )
      & ( ~ r2_hidden(esk7_2(X71,X72),X72)
        | ~ r2_hidden(k4_tarski(X74,esk7_2(X71,X72)),X71)
        | X72 = k2_relat_1(X71) )
      & ( r2_hidden(esk7_2(X71,X72),X72)
        | r2_hidden(k4_tarski(esk8_2(X71,X72),esk7_2(X71,X72)),X71)
        | X72 = k2_relat_1(X71) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_45,plain,(
    ! [X38,X39] :
      ( ( ~ r1_xboole_0(X38,X39)
        | k4_xboole_0(X38,X39) = X38 )
      & ( k4_xboole_0(X38,X39) != X38
        | r1_xboole_0(X38,X39) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_46,plain,
    ( X1 != k2_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1)
    | ~ r1_xboole_0(k1_xboole_0,X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_48,plain,
    ( X1 != k2_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_41])])).

fof(c_0_49,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_52,plain,(
    ! [X48,X49] : k3_tarski(k2_tarski(X48,X49)) = k2_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_53,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_54,plain,(
    ! [X54,X55,X56,X58,X59,X60,X61,X63] :
      ( ( ~ r2_hidden(X56,X55)
        | r2_hidden(k4_tarski(X56,esk3_3(X54,X55,X56)),X54)
        | X55 != k1_relat_1(X54) )
      & ( ~ r2_hidden(k4_tarski(X58,X59),X54)
        | r2_hidden(X58,X55)
        | X55 != k1_relat_1(X54) )
      & ( ~ r2_hidden(esk4_2(X60,X61),X61)
        | ~ r2_hidden(k4_tarski(esk4_2(X60,X61),X63),X60)
        | X61 = k1_relat_1(X60) )
      & ( r2_hidden(esk4_2(X60,X61),X61)
        | r2_hidden(k4_tarski(esk4_2(X60,X61),esk5_2(X60,X61)),X60)
        | X61 = k1_relat_1(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_55,plain,(
    ! [X40,X41,X42] :
      ( ~ r1_tarski(X40,X41)
      | ~ r1_tarski(X42,X41)
      | r1_tarski(k2_xboole_0(X40,X42),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_56,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_57,plain,(
    ! [X76] :
      ( ~ v1_relat_1(X76)
      | k3_relat_1(X76) = k2_xboole_0(k1_relat_1(X76),k2_relat_1(X76)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_58,plain,(
    ! [X77,X78] :
      ( ~ v1_relat_1(X77)
      | ~ v1_relat_1(X78)
      | r1_tarski(k6_subset_1(k1_relat_1(X77),k1_relat_1(X78)),k1_relat_1(k6_subset_1(X77,X78))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).

fof(c_0_59,plain,(
    ! [X50,X51] : k6_subset_1(X50,X51) = k4_xboole_0(X50,X51) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_53])).

cnf(c_0_61,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_62,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

cnf(c_0_63,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_56,c_0_27])).

cnf(c_0_65,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_66,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | r1_tarski(X18,k2_xboole_0(X20,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_67,plain,(
    ! [X31,X32,X33] :
      ( ~ r1_tarski(k4_xboole_0(X31,X32),X33)
      | r1_tarski(X31,k2_xboole_0(X32,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_68,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_69,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_72,plain,(
    ! [X79,X80] :
      ( ~ v1_relat_1(X79)
      | ~ v1_relat_1(X80)
      | r1_tarski(k6_subset_1(k2_relat_1(X79),k2_relat_1(X80)),k2_relat_1(k6_subset_1(X79,X80))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).

fof(c_0_73,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & v1_relat_1(esk10_0)
    & r1_tarski(esk9_0,esk10_0)
    & ~ r1_tarski(k3_relat_1(esk9_0),k3_relat_1(esk10_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_62])])])).

cnf(c_0_74,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_32])).

cnf(c_0_75,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_64]),c_0_32])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_70])).

fof(c_0_80,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(X16,X17) != k1_xboole_0
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | k4_xboole_0(X16,X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_71])).

fof(c_0_82,plain,(
    ! [X24] : r1_tarski(k1_xboole_0,X24) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_83,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk9_0),k3_relat_1(esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_85,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_86,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X3,X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_64]),c_0_32])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_64]),c_0_32])).

cnf(c_0_89,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_90,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_91,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_51])).

cnf(c_0_92,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_93,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_70]),c_0_70])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk9_0),k3_relat_1(esk10_0))
    | ~ r1_tarski(k1_relat_1(esk9_0),k3_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_75])).

cnf(c_0_96,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_75])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91]),c_0_91]),c_0_92])])).

cnf(c_0_99,plain,
    ( k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) = k2_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk9_0),k3_relat_1(esk10_0))
    | ~ r1_tarski(k2_relat_1(esk9_0),k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])])).

cnf(c_0_101,plain,
    ( r1_tarski(k1_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_92])])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_103,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_104,plain,
    ( k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_90]),c_0_53]),c_0_53]),c_0_92])])).

cnf(c_0_105,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk9_0),k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_96]),c_0_86]),c_0_102])])).

cnf(c_0_106,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_96]),c_0_86]),c_0_102])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:10:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 1.29/1.50  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 1.29/1.50  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.29/1.50  #
% 1.29/1.50  # Preprocessing time       : 0.029 s
% 1.29/1.50  
% 1.29/1.50  # Proof found!
% 1.29/1.50  # SZS status Theorem
% 1.29/1.50  # SZS output start CNFRefutation
% 1.29/1.50  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.29/1.50  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.29/1.50  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.29/1.50  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.29/1.50  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.29/1.50  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.29/1.50  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.29/1.50  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 1.29/1.50  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.29/1.50  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.29/1.50  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.29/1.50  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.29/1.50  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.29/1.50  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.29/1.50  fof(t15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 1.29/1.50  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.29/1.50  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 1.29/1.50  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.29/1.50  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.29/1.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.29/1.50  fof(t28_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 1.29/1.50  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.29/1.50  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.29/1.50  fof(c_0_23, plain, ![X52, X53]:k1_setfam_1(k2_tarski(X52,X53))=k3_xboole_0(X52,X53), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.29/1.50  fof(c_0_24, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.29/1.50  fof(c_0_25, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 1.29/1.50  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.29/1.50  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.29/1.50  fof(c_0_28, plain, ![X45, X46, X47]:k2_enumset1(X45,X45,X46,X47)=k1_enumset1(X45,X46,X47), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.29/1.50  fof(c_0_29, plain, ![X34, X35]:k4_xboole_0(X34,k4_xboole_0(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.29/1.50  cnf(c_0_30, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.29/1.50  cnf(c_0_31, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 1.29/1.50  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.29/1.50  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.29/1.50  fof(c_0_34, plain, ![X27]:(~r1_tarski(X27,k1_xboole_0)|X27=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 1.29/1.50  fof(c_0_35, plain, ![X25, X26]:r1_tarski(k4_xboole_0(X25,X26),X25), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.29/1.50  cnf(c_0_36, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 1.29/1.50  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_31]), c_0_32])).
% 1.29/1.50  cnf(c_0_38, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.29/1.50  cnf(c_0_39, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.29/1.50  cnf(c_0_40, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X2,X3)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 1.29/1.50  cnf(c_0_41, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.29/1.50  fof(c_0_42, plain, ![X65, X66, X67, X69, X70, X71, X72, X74]:(((~r2_hidden(X67,X66)|r2_hidden(k4_tarski(esk6_3(X65,X66,X67),X67),X65)|X66!=k2_relat_1(X65))&(~r2_hidden(k4_tarski(X70,X69),X65)|r2_hidden(X69,X66)|X66!=k2_relat_1(X65)))&((~r2_hidden(esk7_2(X71,X72),X72)|~r2_hidden(k4_tarski(X74,esk7_2(X71,X72)),X71)|X72=k2_relat_1(X71))&(r2_hidden(esk7_2(X71,X72),X72)|r2_hidden(k4_tarski(esk8_2(X71,X72),esk7_2(X71,X72)),X71)|X72=k2_relat_1(X71)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 1.29/1.50  cnf(c_0_43, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.29/1.50  cnf(c_0_44, plain, (r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.29/1.50  fof(c_0_45, plain, ![X38, X39]:((~r1_xboole_0(X38,X39)|k4_xboole_0(X38,X39)=X38)&(k4_xboole_0(X38,X39)!=X38|r1_xboole_0(X38,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 1.29/1.50  cnf(c_0_46, plain, (X1!=k2_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)|~r1_xboole_0(k1_xboole_0,X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.29/1.50  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.29/1.50  cnf(c_0_48, plain, (X1!=k2_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_41])])).
% 1.29/1.50  fof(c_0_49, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 1.29/1.50  cnf(c_0_50, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_48])).
% 1.29/1.50  cnf(c_0_51, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.29/1.50  fof(c_0_52, plain, ![X48, X49]:k3_tarski(k2_tarski(X48,X49))=k2_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.29/1.50  cnf(c_0_53, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.29/1.50  fof(c_0_54, plain, ![X54, X55, X56, X58, X59, X60, X61, X63]:(((~r2_hidden(X56,X55)|r2_hidden(k4_tarski(X56,esk3_3(X54,X55,X56)),X54)|X55!=k1_relat_1(X54))&(~r2_hidden(k4_tarski(X58,X59),X54)|r2_hidden(X58,X55)|X55!=k1_relat_1(X54)))&((~r2_hidden(esk4_2(X60,X61),X61)|~r2_hidden(k4_tarski(esk4_2(X60,X61),X63),X60)|X61=k1_relat_1(X60))&(r2_hidden(esk4_2(X60,X61),X61)|r2_hidden(k4_tarski(esk4_2(X60,X61),esk5_2(X60,X61)),X60)|X61=k1_relat_1(X60)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.29/1.50  fof(c_0_55, plain, ![X40, X41, X42]:(~r1_tarski(X40,X41)|~r1_tarski(X42,X41)|r1_tarski(k2_xboole_0(X40,X42),X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 1.29/1.50  cnf(c_0_56, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.29/1.50  fof(c_0_57, plain, ![X76]:(~v1_relat_1(X76)|k3_relat_1(X76)=k2_xboole_0(k1_relat_1(X76),k2_relat_1(X76))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 1.29/1.50  fof(c_0_58, plain, ![X77, X78]:(~v1_relat_1(X77)|(~v1_relat_1(X78)|r1_tarski(k6_subset_1(k1_relat_1(X77),k1_relat_1(X78)),k1_relat_1(k6_subset_1(X77,X78))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).
% 1.29/1.50  fof(c_0_59, plain, ![X50, X51]:k6_subset_1(X50,X51)=k4_xboole_0(X50,X51), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 1.29/1.50  cnf(c_0_60, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_50, c_0_53])).
% 1.29/1.50  cnf(c_0_61, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.29/1.50  fof(c_0_62, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 1.29/1.50  cnf(c_0_63, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.29/1.50  cnf(c_0_64, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_56, c_0_27])).
% 1.29/1.50  cnf(c_0_65, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.29/1.50  fof(c_0_66, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|r1_tarski(X18,k2_xboole_0(X20,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 1.29/1.50  fof(c_0_67, plain, ![X31, X32, X33]:(~r1_tarski(k4_xboole_0(X31,X32),X33)|r1_tarski(X31,k2_xboole_0(X32,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 1.29/1.50  fof(c_0_68, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.29/1.50  cnf(c_0_69, plain, (r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.29/1.50  cnf(c_0_70, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.29/1.50  cnf(c_0_71, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 1.29/1.50  fof(c_0_72, plain, ![X79, X80]:(~v1_relat_1(X79)|(~v1_relat_1(X80)|r1_tarski(k6_subset_1(k2_relat_1(X79),k2_relat_1(X80)),k2_relat_1(k6_subset_1(X79,X80))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).
% 1.29/1.50  fof(c_0_73, negated_conjecture, (v1_relat_1(esk9_0)&(v1_relat_1(esk10_0)&(r1_tarski(esk9_0,esk10_0)&~r1_tarski(k3_relat_1(esk9_0),k3_relat_1(esk10_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_62])])])).
% 1.29/1.50  cnf(c_0_74, plain, (r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_32])).
% 1.29/1.50  cnf(c_0_75, plain, (k3_relat_1(X1)=k3_tarski(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_64]), c_0_32])).
% 1.29/1.50  cnf(c_0_76, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 1.29/1.50  cnf(c_0_77, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 1.29/1.50  cnf(c_0_78, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 1.29/1.50  cnf(c_0_79, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_70])).
% 1.29/1.50  fof(c_0_80, plain, ![X16, X17]:((k4_xboole_0(X16,X17)!=k1_xboole_0|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|k4_xboole_0(X16,X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.29/1.50  cnf(c_0_81, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_71])).
% 1.29/1.50  fof(c_0_82, plain, ![X24]:r1_tarski(k1_xboole_0,X24), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.29/1.50  cnf(c_0_83, plain, (r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.29/1.50  cnf(c_0_84, negated_conjecture, (~r1_tarski(k3_relat_1(esk9_0),k3_relat_1(esk10_0))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.29/1.50  cnf(c_0_85, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 1.29/1.50  cnf(c_0_86, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.29/1.50  cnf(c_0_87, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X3,X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_64]), c_0_32])).
% 1.29/1.50  cnf(c_0_88, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_64]), c_0_32])).
% 1.29/1.50  cnf(c_0_89, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 1.29/1.50  cnf(c_0_90, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.29/1.50  cnf(c_0_91, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_51])).
% 1.29/1.50  cnf(c_0_92, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.29/1.50  cnf(c_0_93, plain, (r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_70]), c_0_70])).
% 1.29/1.50  cnf(c_0_94, negated_conjecture, (~r1_tarski(k2_relat_1(esk9_0),k3_relat_1(esk10_0))|~r1_tarski(k1_relat_1(esk9_0),k3_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])])).
% 1.29/1.50  cnf(c_0_95, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_87, c_0_75])).
% 1.29/1.50  cnf(c_0_96, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.29/1.50  cnf(c_0_97, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_88, c_0_75])).
% 1.29/1.50  cnf(c_0_98, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91]), c_0_91]), c_0_92])])).
% 1.29/1.50  cnf(c_0_99, plain, (k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=k2_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), inference(spm,[status(thm)],[c_0_78, c_0_93])).
% 1.29/1.50  cnf(c_0_100, negated_conjecture, (~r1_tarski(k1_relat_1(esk9_0),k3_relat_1(esk10_0))|~r1_tarski(k2_relat_1(esk9_0),k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])])).
% 1.29/1.50  cnf(c_0_101, plain, (r1_tarski(k1_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_92])])).
% 1.29/1.50  cnf(c_0_102, negated_conjecture, (r1_tarski(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.29/1.50  cnf(c_0_103, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.29/1.50  cnf(c_0_104, plain, (k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_90]), c_0_53]), c_0_53]), c_0_92])])).
% 1.29/1.50  cnf(c_0_105, negated_conjecture, (~r1_tarski(k2_relat_1(esk9_0),k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_96]), c_0_86]), c_0_102])])).
% 1.29/1.50  cnf(c_0_106, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 1.29/1.50  cnf(c_0_107, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_96]), c_0_86]), c_0_102])]), ['proof']).
% 1.29/1.50  # SZS output end CNFRefutation
% 1.29/1.50  # Proof object total steps             : 108
% 1.29/1.50  # Proof object clause steps            : 61
% 1.29/1.50  # Proof object formula steps           : 47
% 1.29/1.50  # Proof object conjectures             : 11
% 1.29/1.50  # Proof object clause conjectures      : 8
% 1.29/1.50  # Proof object formula conjectures     : 3
% 1.29/1.50  # Proof object initial clauses used    : 27
% 1.29/1.50  # Proof object initial formulas used   : 23
% 1.29/1.50  # Proof object generating inferences   : 22
% 1.29/1.50  # Proof object simplifying inferences  : 44
% 1.29/1.50  # Training examples: 0 positive, 0 negative
% 1.29/1.50  # Parsed axioms                        : 27
% 1.29/1.50  # Removed by relevancy pruning/SinE    : 0
% 1.29/1.50  # Initial clauses                      : 41
% 1.29/1.50  # Removed in clause preprocessing      : 5
% 1.29/1.50  # Initial clauses in saturation        : 36
% 1.29/1.50  # Processed clauses                    : 5837
% 1.29/1.50  # ...of these trivial                  : 90
% 1.29/1.50  # ...subsumed                          : 4391
% 1.29/1.50  # ...remaining for further processing  : 1356
% 1.29/1.50  # Other redundant clauses eliminated   : 2
% 1.29/1.50  # Clauses deleted for lack of memory   : 0
% 1.29/1.50  # Backward-subsumed                    : 82
% 1.29/1.50  # Backward-rewritten                   : 31
% 1.29/1.50  # Generated clauses                    : 89131
% 1.29/1.50  # ...of the previous two non-trivial   : 78588
% 1.29/1.50  # Contextual simplify-reflections      : 59
% 1.29/1.50  # Paramodulations                      : 89063
% 1.29/1.50  # Factorizations                       : 8
% 1.29/1.50  # Equation resolutions                 : 60
% 1.29/1.50  # Propositional unsat checks           : 0
% 1.29/1.50  #    Propositional check models        : 0
% 1.29/1.50  #    Propositional check unsatisfiable : 0
% 1.29/1.50  #    Propositional clauses             : 0
% 1.29/1.50  #    Propositional clauses after purity: 0
% 1.29/1.50  #    Propositional unsat core size     : 0
% 1.29/1.50  #    Propositional preprocessing time  : 0.000
% 1.29/1.50  #    Propositional encoding time       : 0.000
% 1.29/1.50  #    Propositional solver time         : 0.000
% 1.29/1.50  #    Success case prop preproc time    : 0.000
% 1.29/1.50  #    Success case prop encoding time   : 0.000
% 1.29/1.50  #    Success case prop solver time     : 0.000
% 1.29/1.50  # Current number of processed clauses  : 1241
% 1.29/1.50  #    Positive orientable unit clauses  : 88
% 1.29/1.50  #    Positive unorientable unit clauses: 0
% 1.29/1.50  #    Negative unit clauses             : 21
% 1.29/1.50  #    Non-unit-clauses                  : 1132
% 1.29/1.50  # Current number of unprocessed clauses: 72280
% 1.29/1.50  # ...number of literals in the above   : 282040
% 1.29/1.50  # Current number of archived formulas  : 0
% 1.29/1.50  # Current number of archived clauses   : 118
% 1.29/1.50  # Clause-clause subsumption calls (NU) : 363012
% 1.29/1.50  # Rec. Clause-clause subsumption calls : 147529
% 1.29/1.50  # Non-unit clause-clause subsumptions  : 2739
% 1.29/1.50  # Unit Clause-clause subsumption calls : 6502
% 1.29/1.50  # Rewrite failures with RHS unbound    : 0
% 1.29/1.50  # BW rewrite match attempts            : 1555
% 1.29/1.50  # BW rewrite match successes           : 14
% 1.29/1.50  # Condensation attempts                : 0
% 1.29/1.50  # Condensation successes               : 0
% 1.29/1.50  # Termbank termtop insertions          : 1542160
% 1.29/1.50  
% 1.29/1.50  # -------------------------------------------------
% 1.29/1.50  # User time                : 1.105 s
% 1.29/1.50  # System time              : 0.057 s
% 1.29/1.50  # Total time               : 1.161 s
% 1.29/1.50  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
