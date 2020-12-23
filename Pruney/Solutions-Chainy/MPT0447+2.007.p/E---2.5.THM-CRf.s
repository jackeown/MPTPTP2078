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
% DateTime   : Thu Dec  3 10:48:22 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 396 expanded)
%              Number of clauses        :   75 ( 187 expanded)
%              Number of leaves         :   21 ( 100 expanded)
%              Depth                    :   17
%              Number of atoms          :  288 (1025 expanded)
%              Number of equality atoms :   47 ( 209 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r2_hidden(X1,k2_relat_1(X2))
          & ! [X3] : ~ r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t28_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(t15_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_21,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_22,plain,(
    ! [X47,X48,X50] :
      ( ( r2_hidden(esk5_2(X47,X48),X48)
        | ~ r2_hidden(X47,X48) )
      & ( ~ r2_hidden(X50,X48)
        | ~ r2_hidden(X50,esk5_2(X47,X48))
        | ~ r2_hidden(X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(esk5_2(X1,X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_26,plain,(
    ! [X54,X55,X56,X58,X59,X60,X61,X63] :
      ( ( ~ r2_hidden(X56,X55)
        | r2_hidden(k4_tarski(X56,esk6_3(X54,X55,X56)),X54)
        | X55 != k1_relat_1(X54) )
      & ( ~ r2_hidden(k4_tarski(X58,X59),X54)
        | r2_hidden(X58,X55)
        | X55 != k1_relat_1(X54) )
      & ( ~ r2_hidden(esk7_2(X60,X61),X61)
        | ~ r2_hidden(k4_tarski(esk7_2(X60,X61),X63),X60)
        | X61 = k1_relat_1(X60) )
      & ( r2_hidden(esk7_2(X60,X61),X61)
        | r2_hidden(k4_tarski(esk7_2(X60,X61),esk8_2(X60,X61)),X60)
        | X61 = k1_relat_1(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X28] : r1_xboole_0(X28,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( X1 != k1_relat_1(X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,plain,(
    ! [X45,X46] : k3_tarski(k2_tarski(X45,X46)) = k2_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_39,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk2_1(X1),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_34])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | X2 != k1_relat_1(X3)
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_43,plain,(
    ! [X29,X30] : r1_tarski(X29,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_44,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_46,plain,(
    ! [X68,X69] :
      ( ~ v1_relat_1(X69)
      | ~ r2_hidden(X68,k2_relat_1(X69))
      | r2_hidden(esk9_2(X68,X69),k1_relat_1(X69)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | X2 != k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_49,plain,(
    ! [X53] :
      ( ~ v1_xboole_0(X53)
      | v1_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_50,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_53,plain,(
    ! [X31,X32,X33] :
      ( ~ r1_tarski(X31,X32)
      | ~ r1_tarski(X33,X32)
      | r1_tarski(k2_xboole_0(X31,X33),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_54,plain,(
    ! [X71,X72] :
      ( ~ v1_relat_1(X71)
      | ~ v1_relat_1(X72)
      | r1_tarski(k6_subset_1(k2_relat_1(X71),k2_relat_1(X72)),k2_relat_1(k6_subset_1(X71,X72))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).

fof(c_0_55,plain,(
    ! [X51,X52] : k6_subset_1(X51,X52) = k4_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_56,plain,
    ( r2_hidden(esk9_2(X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_60,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | r1_tarski(X17,k2_xboole_0(X19,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_61,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_65,plain,(
    ! [X65] :
      ( ~ v1_relat_1(X65)
      | k3_relat_1(X65) = k2_xboole_0(k1_relat_1(X65),k2_relat_1(X65)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_66,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_68,plain,(
    ! [X15,X16] :
      ( ( k4_xboole_0(X15,X16) != k1_xboole_0
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | k4_xboole_0(X15,X16) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_69,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r1_xboole_0(k1_relat_1(X1),k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_56])).

cnf(c_0_70,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_74,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_63,c_0_52])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_64])).

fof(c_0_76,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

cnf(c_0_77,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_67])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_42])])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_52])).

cnf(c_0_82,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

fof(c_0_83,plain,(
    ! [X66,X67] :
      ( ~ v1_relat_1(X66)
      | ~ v1_relat_1(X67)
      | r1_tarski(k6_subset_1(k1_relat_1(X66),k1_relat_1(X67)),k1_relat_1(k6_subset_1(X66,X67))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).

fof(c_0_84,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & v1_relat_1(esk11_0)
    & r1_tarski(esk10_0,esk11_0)
    & ~ r1_tarski(k3_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])).

cnf(c_0_85,plain,
    ( k3_relat_1(X1) = k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_77,c_0_52])).

cnf(c_0_86,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_87,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_34])).

fof(c_0_88,plain,(
    ! [X24] : r1_tarski(k1_xboole_0,X24) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_92,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_94,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k1_xboole_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_95,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k3_tarski(k1_enumset1(X3,X3,X4)),X2)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_89,c_0_81])).

cnf(c_0_97,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_67]),c_0_67])).

cnf(c_0_98,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk10_0),k3_relat_1(esk11_0))
    | ~ r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_85])).

cnf(c_0_100,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_102,plain,
    ( k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_94]),c_0_95])])).

cnf(c_0_103,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_96,c_0_82])).

cnf(c_0_104,plain,
    ( r1_tarski(k1_relat_1(X1),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_85])).

cnf(c_0_105,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_97,c_0_79])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0))
    | ~ r1_tarski(k2_relat_1(esk10_0),k2_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])])).

cnf(c_0_107,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(esk10_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_109,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X3,k1_relat_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_110,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_xboole_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_105,c_0_70])).

cnf(c_0_111,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_100]),c_0_93]),c_0_108])])).

cnf(c_0_112,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_75])).

cnf(c_0_113,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_110]),c_0_95])])).

cnf(c_0_114,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk10_0),k1_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_100])])).

cnf(c_0_115,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_113])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_100]),c_0_93]),c_0_108])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.92/1.17  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.92/1.17  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.92/1.17  #
% 0.92/1.17  # Preprocessing time       : 0.029 s
% 0.92/1.17  
% 0.92/1.17  # Proof found!
% 0.92/1.17  # SZS status Theorem
% 0.92/1.17  # SZS output start CNFRefutation
% 0.92/1.17  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.92/1.17  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 0.92/1.17  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.92/1.17  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.92/1.17  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.92/1.17  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.92/1.17  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.92/1.17  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.92/1.17  fof(t19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~((r2_hidden(X1,k2_relat_1(X2))&![X3]:~(r2_hidden(X3,k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 0.92/1.17  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.92/1.17  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.92/1.17  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.92/1.17  fof(t28_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 0.92/1.17  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.92/1.17  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.92/1.17  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.92/1.17  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.92/1.17  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.92/1.17  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 0.92/1.17  fof(t15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 0.92/1.17  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.92/1.17  fof(c_0_21, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.92/1.17  fof(c_0_22, plain, ![X47, X48, X50]:((r2_hidden(esk5_2(X47,X48),X48)|~r2_hidden(X47,X48))&(~r2_hidden(X50,X48)|~r2_hidden(X50,esk5_2(X47,X48))|~r2_hidden(X47,X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.92/1.17  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.92/1.17  cnf(c_0_24, plain, (r2_hidden(esk5_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.92/1.17  cnf(c_0_25, plain, (~r2_hidden(esk5_2(X1,X2),X3)|~r2_hidden(X1,X2)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.92/1.17  fof(c_0_26, plain, ![X54, X55, X56, X58, X59, X60, X61, X63]:(((~r2_hidden(X56,X55)|r2_hidden(k4_tarski(X56,esk6_3(X54,X55,X56)),X54)|X55!=k1_relat_1(X54))&(~r2_hidden(k4_tarski(X58,X59),X54)|r2_hidden(X58,X55)|X55!=k1_relat_1(X54)))&((~r2_hidden(esk7_2(X60,X61),X61)|~r2_hidden(k4_tarski(esk7_2(X60,X61),X63),X60)|X61=k1_relat_1(X60))&(r2_hidden(esk7_2(X60,X61),X61)|r2_hidden(k4_tarski(esk7_2(X60,X61),esk8_2(X60,X61)),X60)|X61=k1_relat_1(X60)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.92/1.17  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.92/1.17  fof(c_0_28, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.92/1.17  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.92/1.17  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,esk6_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.92/1.17  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_23, c_0_27])).
% 0.92/1.17  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.92/1.17  fof(c_0_33, plain, ![X28]:r1_xboole_0(X28,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.92/1.17  cnf(c_0_34, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.17  cnf(c_0_35, plain, (X1!=k1_relat_1(X2)|~r2_hidden(X3,X1)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.92/1.17  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.92/1.17  cnf(c_0_37, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.92/1.17  fof(c_0_38, plain, ![X45, X46]:k3_tarski(k2_tarski(X45,X46))=k2_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.92/1.17  fof(c_0_39, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.92/1.17  cnf(c_0_40, plain, (X1=k1_xboole_0|~r2_hidden(esk2_1(X1),X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_34])).
% 0.92/1.17  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|X2!=k1_relat_1(X3)|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 0.92/1.17  cnf(c_0_42, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.92/1.17  fof(c_0_43, plain, ![X29, X30]:r1_tarski(X29,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.92/1.17  cnf(c_0_44, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.92/1.17  cnf(c_0_45, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.92/1.17  fof(c_0_46, plain, ![X68, X69]:(~v1_relat_1(X69)|(~r2_hidden(X68,k2_relat_1(X69))|r2_hidden(esk9_2(X68,X69),k1_relat_1(X69)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).
% 0.92/1.17  cnf(c_0_47, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.92/1.17  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|X2!=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.92/1.17  fof(c_0_49, plain, ![X53]:(~v1_xboole_0(X53)|v1_relat_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.92/1.17  fof(c_0_50, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.92/1.17  cnf(c_0_51, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.92/1.17  cnf(c_0_52, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.92/1.17  fof(c_0_53, plain, ![X31, X32, X33]:(~r1_tarski(X31,X32)|~r1_tarski(X33,X32)|r1_tarski(k2_xboole_0(X31,X33),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.92/1.17  fof(c_0_54, plain, ![X71, X72]:(~v1_relat_1(X71)|(~v1_relat_1(X72)|r1_tarski(k6_subset_1(k2_relat_1(X71),k2_relat_1(X72)),k2_relat_1(k6_subset_1(X71,X72))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).
% 0.92/1.17  fof(c_0_55, plain, ![X51, X52]:k6_subset_1(X51,X52)=k4_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.92/1.17  cnf(c_0_56, plain, (r2_hidden(esk9_2(X2,X1),k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.92/1.17  cnf(c_0_57, plain, (X1=k1_xboole_0|X1!=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.92/1.17  cnf(c_0_58, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.92/1.17  cnf(c_0_59, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.92/1.17  fof(c_0_60, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|r1_tarski(X17,k2_xboole_0(X19,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.92/1.17  cnf(c_0_61, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.92/1.17  cnf(c_0_62, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.92/1.17  cnf(c_0_63, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.92/1.17  cnf(c_0_64, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.92/1.17  fof(c_0_65, plain, ![X65]:(~v1_relat_1(X65)|k3_relat_1(X65)=k2_xboole_0(k1_relat_1(X65),k2_relat_1(X65))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.92/1.17  cnf(c_0_66, plain, (r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.92/1.17  cnf(c_0_67, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.92/1.17  fof(c_0_68, plain, ![X15, X16]:((k4_xboole_0(X15,X16)!=k1_xboole_0|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|k4_xboole_0(X15,X16)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.92/1.17  cnf(c_0_69, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r1_xboole_0(k1_relat_1(X1),k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_56])).
% 0.92/1.17  cnf(c_0_70, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_57])).
% 0.92/1.17  cnf(c_0_71, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.92/1.17  cnf(c_0_72, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.92/1.17  cnf(c_0_73, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.92/1.17  cnf(c_0_74, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_63, c_0_52])).
% 0.92/1.17  cnf(c_0_75, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_64])).
% 0.92/1.17  fof(c_0_76, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 0.92/1.17  cnf(c_0_77, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.92/1.17  cnf(c_0_78, plain, (r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_67])).
% 0.92/1.17  cnf(c_0_79, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.92/1.17  cnf(c_0_80, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_42])])).
% 0.92/1.17  cnf(c_0_81, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_52])).
% 0.92/1.17  cnf(c_0_82, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])])).
% 0.92/1.17  fof(c_0_83, plain, ![X66, X67]:(~v1_relat_1(X66)|(~v1_relat_1(X67)|r1_tarski(k6_subset_1(k1_relat_1(X66),k1_relat_1(X67)),k1_relat_1(k6_subset_1(X66,X67))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).
% 0.92/1.17  fof(c_0_84, negated_conjecture, (v1_relat_1(esk10_0)&(v1_relat_1(esk11_0)&(r1_tarski(esk10_0,esk11_0)&~r1_tarski(k3_relat_1(esk10_0),k3_relat_1(esk11_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])).
% 0.92/1.17  cnf(c_0_85, plain, (k3_relat_1(X1)=k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_77, c_0_52])).
% 0.92/1.17  cnf(c_0_86, plain, (r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k1_xboole_0))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.92/1.17  cnf(c_0_87, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_80, c_0_34])).
% 0.92/1.17  fof(c_0_88, plain, ![X24]:r1_tarski(k1_xboole_0,X24), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.92/1.17  cnf(c_0_89, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.92/1.17  cnf(c_0_90, plain, (r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.92/1.17  cnf(c_0_91, negated_conjecture, (~r1_tarski(k3_relat_1(esk10_0),k3_relat_1(esk11_0))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.92/1.17  cnf(c_0_92, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_74, c_0_85])).
% 0.92/1.17  cnf(c_0_93, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.92/1.17  cnf(c_0_94, plain, (r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k1_xboole_0)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_86, c_0_87])).
% 0.92/1.17  cnf(c_0_95, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.92/1.17  cnf(c_0_96, plain, (r1_tarski(X1,X2)|~r1_tarski(k3_tarski(k1_enumset1(X3,X3,X4)),X2)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_89, c_0_81])).
% 0.92/1.17  cnf(c_0_97, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_67]), c_0_67])).
% 0.92/1.17  cnf(c_0_98, negated_conjecture, (~r1_tarski(k2_relat_1(esk10_0),k3_relat_1(esk11_0))|~r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])])).
% 0.92/1.17  cnf(c_0_99, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_81, c_0_85])).
% 0.92/1.17  cnf(c_0_100, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.92/1.17  cnf(c_0_101, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.92/1.17  cnf(c_0_102, plain, (k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_94]), c_0_95])])).
% 0.92/1.17  cnf(c_0_103, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_96, c_0_82])).
% 0.92/1.17  cnf(c_0_104, plain, (r1_tarski(k1_relat_1(X1),k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_85])).
% 0.92/1.17  cnf(c_0_105, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k1_xboole_0))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_97, c_0_79])).
% 0.92/1.17  cnf(c_0_106, negated_conjecture, (~r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0))|~r1_tarski(k2_relat_1(esk10_0),k2_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100])])).
% 0.92/1.17  cnf(c_0_107, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.92/1.17  cnf(c_0_108, negated_conjecture, (r1_tarski(esk10_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.92/1.17  cnf(c_0_109, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X3,k1_relat_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.92/1.17  cnf(c_0_110, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_xboole_0)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_105, c_0_70])).
% 0.92/1.17  cnf(c_0_111, negated_conjecture, (~r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_100]), c_0_93]), c_0_108])])).
% 0.92/1.17  cnf(c_0_112, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_109, c_0_75])).
% 0.92/1.17  cnf(c_0_113, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_110]), c_0_95])])).
% 0.92/1.17  cnf(c_0_114, negated_conjecture, (~r1_tarski(k1_relat_1(esk10_0),k1_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_100])])).
% 0.92/1.17  cnf(c_0_115, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_101, c_0_113])).
% 0.92/1.17  cnf(c_0_116, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_100]), c_0_93]), c_0_108])]), ['proof']).
% 0.92/1.17  # SZS output end CNFRefutation
% 0.92/1.17  # Proof object total steps             : 117
% 0.92/1.17  # Proof object clause steps            : 75
% 0.92/1.17  # Proof object formula steps           : 42
% 0.92/1.17  # Proof object conjectures             : 12
% 0.92/1.17  # Proof object clause conjectures      : 9
% 0.92/1.17  # Proof object formula conjectures     : 3
% 0.92/1.17  # Proof object initial clauses used    : 28
% 0.92/1.17  # Proof object initial formulas used   : 21
% 0.92/1.17  # Proof object generating inferences   : 37
% 0.92/1.17  # Proof object simplifying inferences  : 35
% 0.92/1.17  # Training examples: 0 positive, 0 negative
% 0.92/1.17  # Parsed axioms                        : 24
% 0.92/1.17  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.17  # Initial clauses                      : 43
% 0.92/1.17  # Removed in clause preprocessing      : 3
% 0.92/1.17  # Initial clauses in saturation        : 40
% 0.92/1.17  # Processed clauses                    : 1693
% 0.92/1.17  # ...of these trivial                  : 16
% 0.92/1.17  # ...subsumed                          : 973
% 0.92/1.17  # ...remaining for further processing  : 704
% 0.92/1.17  # Other redundant clauses eliminated   : 260
% 0.92/1.17  # Clauses deleted for lack of memory   : 0
% 0.92/1.17  # Backward-subsumed                    : 42
% 0.92/1.17  # Backward-rewritten                   : 25
% 0.92/1.17  # Generated clauses                    : 36212
% 0.92/1.17  # ...of the previous two non-trivial   : 33755
% 0.92/1.17  # Contextual simplify-reflections      : 5
% 0.92/1.17  # Paramodulations                      : 35660
% 0.92/1.17  # Factorizations                       : 235
% 0.92/1.17  # Equation resolutions                 : 317
% 0.92/1.17  # Propositional unsat checks           : 0
% 0.92/1.17  #    Propositional check models        : 0
% 0.92/1.17  #    Propositional check unsatisfiable : 0
% 0.92/1.17  #    Propositional clauses             : 0
% 0.92/1.17  #    Propositional clauses after purity: 0
% 0.92/1.17  #    Propositional unsat core size     : 0
% 0.92/1.17  #    Propositional preprocessing time  : 0.000
% 0.92/1.17  #    Propositional encoding time       : 0.000
% 0.92/1.17  #    Propositional solver time         : 0.000
% 0.92/1.17  #    Success case prop preproc time    : 0.000
% 0.92/1.17  #    Success case prop encoding time   : 0.000
% 0.92/1.17  #    Success case prop solver time     : 0.000
% 0.92/1.17  # Current number of processed clauses  : 633
% 0.92/1.17  #    Positive orientable unit clauses  : 33
% 0.92/1.17  #    Positive unorientable unit clauses: 0
% 0.92/1.17  #    Negative unit clauses             : 17
% 0.92/1.17  #    Non-unit-clauses                  : 583
% 0.92/1.17  # Current number of unprocessed clauses: 31944
% 0.92/1.17  # ...number of literals in the above   : 240388
% 0.92/1.17  # Current number of archived formulas  : 0
% 0.92/1.17  # Current number of archived clauses   : 70
% 0.92/1.17  # Clause-clause subsumption calls (NU) : 61481
% 0.92/1.17  # Rec. Clause-clause subsumption calls : 22293
% 0.92/1.17  # Non-unit clause-clause subsumptions  : 777
% 0.92/1.17  # Unit Clause-clause subsumption calls : 2978
% 0.92/1.17  # Rewrite failures with RHS unbound    : 0
% 0.92/1.17  # BW rewrite match attempts            : 170
% 0.92/1.17  # BW rewrite match successes           : 12
% 0.92/1.17  # Condensation attempts                : 0
% 0.92/1.17  # Condensation successes               : 0
% 0.92/1.17  # Termbank termtop insertions          : 789379
% 0.92/1.17  
% 0.92/1.17  # -------------------------------------------------
% 0.92/1.17  # User time                : 0.815 s
% 0.92/1.17  # System time              : 0.023 s
% 0.92/1.17  # Total time               : 0.838 s
% 0.92/1.17  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
