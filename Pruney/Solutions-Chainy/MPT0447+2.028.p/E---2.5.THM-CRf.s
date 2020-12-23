%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:25 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 724 expanded)
%              Number of clauses        :   81 ( 341 expanded)
%              Number of leaves         :   22 ( 183 expanded)
%              Depth                    :   22
%              Number of atoms          :  297 (1406 expanded)
%              Number of equality atoms :   81 ( 530 expanded)
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

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

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

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

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

fof(t26_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_22,plain,(
    ! [X44,X45] : k1_setfam_1(k2_tarski(X44,X45)) = k3_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_23,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r1_xboole_0(X5,X6)
        | r2_hidden(esk1_2(X5,X6),k3_xboole_0(X5,X6)) )
      & ( ~ r2_hidden(X10,k3_xboole_0(X8,X9))
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_29,plain,(
    ! [X46,X47,X48,X50,X51,X52,X53,X55] :
      ( ( ~ r2_hidden(X48,X47)
        | r2_hidden(k4_tarski(X48,esk4_3(X46,X47,X48)),X46)
        | X47 != k1_relat_1(X46) )
      & ( ~ r2_hidden(k4_tarski(X50,X51),X46)
        | r2_hidden(X50,X47)
        | X47 != k1_relat_1(X46) )
      & ( ~ r2_hidden(esk5_2(X52,X53),X53)
        | ~ r2_hidden(k4_tarski(esk5_2(X52,X53),X55),X52)
        | X53 = k1_relat_1(X52) )
      & ( r2_hidden(esk5_2(X52,X53),X53)
        | r2_hidden(k4_tarski(esk5_2(X52,X53),esk6_2(X52,X53)),X52)
        | X53 = k1_relat_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_30,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_31,plain,(
    ! [X36,X37] : k2_tarski(X36,X37) = k2_tarski(X37,X36) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_32,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( X1 != k1_relat_1(k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ r2_hidden(X4,X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_26]),c_0_26])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1)
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_38])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_28])).

fof(c_0_43,plain,(
    ! [X30] : r1_xboole_0(X30,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
    | ~ r1_xboole_0(X2,X3) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_34])).

cnf(c_0_48,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_49,plain,(
    ! [X40,X41] : k3_tarski(k2_tarski(X40,X41)) = k2_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_50,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_51,plain,(
    ! [X33,X34,X35] :
      ( ~ r1_tarski(X33,X34)
      | ~ r1_tarski(X35,X34)
      | r1_tarski(k2_xboole_0(X33,X35),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_52,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_53,plain,(
    ! [X57] :
      ( ~ v1_relat_1(X57)
      | k3_relat_1(X57) = k2_xboole_0(k1_relat_1(X57),k2_relat_1(X57)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_54,plain,(
    ! [X31,X32] : r1_tarski(X31,k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_55,plain,(
    ! [X18,X19,X20] :
      ( ( r1_tarski(X18,esk3_3(X18,X19,X20))
        | ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X20,X19)
        | X19 = k2_xboole_0(X18,X20) )
      & ( r1_tarski(X20,esk3_3(X18,X19,X20))
        | ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X20,X19)
        | X19 = k2_xboole_0(X18,X20) )
      & ( ~ r1_tarski(X19,esk3_3(X18,X19,X20))
        | ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X20,X19)
        | X19 = k2_xboole_0(X18,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

fof(c_0_56,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

cnf(c_0_57,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1)
    | ~ r1_xboole_0(X3,X4) ),
    inference(rw,[status(thm)],[c_0_40,c_0_50])).

cnf(c_0_58,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_26])).

cnf(c_0_60,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_61,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | r1_tarski(X15,k2_xboole_0(X17,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_63,plain,(
    ! [X60,X61] :
      ( ~ v1_relat_1(X60)
      | ~ v1_relat_1(X61)
      | k2_relat_1(k2_xboole_0(X60,X61)) = k2_xboole_0(k2_relat_1(X60),k2_relat_1(X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,esk3_3(X1,X2,X3))
    | X2 = k2_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_65,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_relat_1(esk8_0)
    & r1_tarski(esk7_0,esk8_0)
    & ~ r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).

fof(c_0_66,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_67,plain,(
    ! [X58,X59] :
      ( ~ v1_relat_1(X58)
      | ~ v1_relat_1(X59)
      | r1_tarski(k6_subset_1(k1_relat_1(X58),k1_relat_1(X59)),k1_relat_1(k6_subset_1(X58,X59))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).

fof(c_0_68,plain,(
    ! [X42,X43] : k6_subset_1(X42,X43) = k4_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_69,plain,
    ( X1 != k1_relat_1(X2)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X3,X1)
    | ~ r1_xboole_0(X4,X5) ),
    inference(spm,[status(thm)],[c_0_57,c_0_33])).

cnf(c_0_70,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_71,plain,
    ( k3_relat_1(X1) = k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_59])).

cnf(c_0_74,plain,
    ( k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( X2 = k3_tarski(k1_enumset1(X1,X1,X3))
    | r1_tarski(X1,esk3_3(X1,X2,X3))
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_78,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(k4_xboole_0(X27,X28),X29)
      | r1_tarski(X27,k2_xboole_0(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_79,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_80,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_relat_1(X2)
    | X2 != k1_xboole_0
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_69,c_0_34])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_83,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_84,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_59])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_38])).

cnf(c_0_87,plain,
    ( k2_relat_1(k3_tarski(k1_enumset1(X1,X1,X2))) = k3_tarski(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_59]),c_0_59])).

cnf(c_0_88,negated_conjecture,
    ( k3_tarski(k1_enumset1(X1,X1,esk7_0)) = esk8_0
    | r1_tarski(X1,esk3_3(X1,esk8_0,esk7_0))
    | ~ r1_tarski(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_91,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_92,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_80])).

cnf(c_0_93,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_relat_1(X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_48])).

fof(c_0_94,plain,(
    ! [X22] : r1_tarski(k1_xboole_0,X22) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk7_0),k3_relat_1(esk8_0))
    | ~ r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_71])).

cnf(c_0_97,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_98,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(k3_tarski(k1_enumset1(X2,X2,X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_99,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk8_0,esk8_0,esk7_0)) = esk8_0
    | r1_tarski(esk8_0,esk3_3(esk8_0,esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_100,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_90,c_0_59])).

cnf(c_0_101,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_102,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_93])).

cnf(c_0_103,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0))
    | ~ r1_tarski(k2_relat_1(esk7_0),k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(esk8_0,esk3_3(esk8_0,esk8_0,esk7_0))
    | r1_tarski(k2_relat_1(esk7_0),k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_84]),c_0_97])])).

cnf(c_0_106,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_71])).

cnf(c_0_107,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_xboole_0
    | k4_xboole_0(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103])])).

cnf(c_0_108,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk3_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(esk8_0,esk3_3(esk8_0,esk8_0,esk7_0))
    | ~ r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_110,plain,
    ( r1_tarski(k1_relat_1(X1),k3_relat_1(X2))
    | k4_xboole_0(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_103])])).

fof(c_0_111,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,k2_xboole_0(X25,X26))
      | r1_tarski(k4_xboole_0(X24,X25),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_112,plain,
    ( X1 = k3_tarski(k1_enumset1(X2,X2,X3))
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,esk3_3(X2,X1,X3)) ),
    inference(rw,[status(thm)],[c_0_108,c_0_59])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(esk8_0,esk3_3(esk8_0,esk8_0,esk7_0))
    | k4_xboole_0(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_97]),c_0_84])])).

cnf(c_0_114,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk8_0,esk8_0,esk7_0)) = esk8_0
    | k4_xboole_0(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_76]),c_0_89])])).

cnf(c_0_116,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_114,c_0_59])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),k2_relat_1(esk8_0))
    | k4_xboole_0(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_115]),c_0_84]),c_0_97])])).

fof(c_0_118,plain,(
    ! [X23] :
      ( ~ r1_tarski(X23,k1_xboole_0)
      | X23 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_119,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_38])).

cnf(c_0_120,negated_conjecture,
    ( k4_xboole_0(esk7_0,esk8_0) != k1_xboole_0
    | ~ r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_117])).

cnf(c_0_121,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_122,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_119,c_0_85])).

cnf(c_0_123,negated_conjecture,
    ( k4_xboole_0(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_110]),c_0_97]),c_0_84])])).

cnf(c_0_124,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_125,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.37/0.56  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.37/0.56  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.37/0.56  #
% 0.37/0.56  # Preprocessing time       : 0.029 s
% 0.37/0.56  
% 0.37/0.56  # Proof found!
% 0.37/0.56  # SZS status Theorem
% 0.37/0.56  # SZS output start CNFRefutation
% 0.37/0.56  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.37/0.56  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.37/0.56  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.37/0.56  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.37/0.56  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.37/0.56  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.37/0.56  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.37/0.56  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.37/0.56  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.37/0.56  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.37/0.56  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.37/0.56  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.37/0.56  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 0.37/0.56  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.37/0.56  fof(t26_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 0.37/0.56  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.37/0.56  fof(t15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 0.37/0.56  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.37/0.56  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.37/0.56  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.37/0.56  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.37/0.56  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.37/0.56  fof(c_0_22, plain, ![X44, X45]:k1_setfam_1(k2_tarski(X44,X45))=k3_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.37/0.56  fof(c_0_23, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.37/0.56  fof(c_0_24, plain, ![X5, X6, X8, X9, X10]:((r1_xboole_0(X5,X6)|r2_hidden(esk1_2(X5,X6),k3_xboole_0(X5,X6)))&(~r2_hidden(X10,k3_xboole_0(X8,X9))|~r1_xboole_0(X8,X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.37/0.56  cnf(c_0_25, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.56  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.56  cnf(c_0_27, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  cnf(c_0_28, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.37/0.56  fof(c_0_29, plain, ![X46, X47, X48, X50, X51, X52, X53, X55]:(((~r2_hidden(X48,X47)|r2_hidden(k4_tarski(X48,esk4_3(X46,X47,X48)),X46)|X47!=k1_relat_1(X46))&(~r2_hidden(k4_tarski(X50,X51),X46)|r2_hidden(X50,X47)|X47!=k1_relat_1(X46)))&((~r2_hidden(esk5_2(X52,X53),X53)|~r2_hidden(k4_tarski(esk5_2(X52,X53),X55),X52)|X53=k1_relat_1(X52))&(r2_hidden(esk5_2(X52,X53),X53)|r2_hidden(k4_tarski(esk5_2(X52,X53),esk6_2(X52,X53)),X52)|X53=k1_relat_1(X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.37/0.56  fof(c_0_30, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.37/0.56  fof(c_0_31, plain, ![X36, X37]:k2_tarski(X36,X37)=k2_tarski(X37,X36), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.37/0.56  cnf(c_0_32, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.37/0.56  cnf(c_0_33, plain, (r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.56  cnf(c_0_34, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.37/0.56  cnf(c_0_35, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.37/0.56  cnf(c_0_36, plain, (X1!=k1_relat_1(k1_setfam_1(k1_enumset1(X2,X2,X3)))|~r2_hidden(X4,X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.37/0.56  cnf(c_0_37, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_34])).
% 0.37/0.56  cnf(c_0_38, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_26]), c_0_26])).
% 0.37/0.56  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.56  cnf(c_0_40, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.37/0.56  cnf(c_0_41, plain, (~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_32, c_0_38])).
% 0.37/0.56  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_39, c_0_28])).
% 0.37/0.56  fof(c_0_43, plain, ![X30]:r1_xboole_0(X30,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.37/0.56  cnf(c_0_44, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))|~r1_xboole_0(X2,X3)), inference(er,[status(thm)],[c_0_40])).
% 0.37/0.56  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.37/0.56  cnf(c_0_46, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.37/0.56  cnf(c_0_47, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_34])).
% 0.37/0.56  cnf(c_0_48, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.37/0.56  fof(c_0_49, plain, ![X40, X41]:k3_tarski(k2_tarski(X40,X41))=k2_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.37/0.56  cnf(c_0_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.37/0.56  fof(c_0_51, plain, ![X33, X34, X35]:(~r1_tarski(X33,X34)|~r1_tarski(X35,X34)|r1_tarski(k2_xboole_0(X33,X35),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.37/0.56  cnf(c_0_52, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.37/0.56  fof(c_0_53, plain, ![X57]:(~v1_relat_1(X57)|k3_relat_1(X57)=k2_xboole_0(k1_relat_1(X57),k2_relat_1(X57))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.37/0.56  fof(c_0_54, plain, ![X31, X32]:r1_tarski(X31,k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.37/0.56  fof(c_0_55, plain, ![X18, X19, X20]:(((r1_tarski(X18,esk3_3(X18,X19,X20))|(~r1_tarski(X18,X19)|~r1_tarski(X20,X19))|X19=k2_xboole_0(X18,X20))&(r1_tarski(X20,esk3_3(X18,X19,X20))|(~r1_tarski(X18,X19)|~r1_tarski(X20,X19))|X19=k2_xboole_0(X18,X20)))&(~r1_tarski(X19,esk3_3(X18,X19,X20))|(~r1_tarski(X18,X19)|~r1_tarski(X20,X19))|X19=k2_xboole_0(X18,X20))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 0.37/0.56  fof(c_0_56, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 0.37/0.56  cnf(c_0_57, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)|~r1_xboole_0(X3,X4)), inference(rw,[status(thm)],[c_0_40, c_0_50])).
% 0.37/0.56  cnf(c_0_58, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.37/0.56  cnf(c_0_59, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_52, c_0_26])).
% 0.37/0.56  cnf(c_0_60, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.37/0.56  fof(c_0_61, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|r1_tarski(X15,k2_xboole_0(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.37/0.56  cnf(c_0_62, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.37/0.56  fof(c_0_63, plain, ![X60, X61]:(~v1_relat_1(X60)|(~v1_relat_1(X61)|k2_relat_1(k2_xboole_0(X60,X61))=k2_xboole_0(k2_relat_1(X60),k2_relat_1(X61)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).
% 0.37/0.56  cnf(c_0_64, plain, (r1_tarski(X1,esk3_3(X1,X2,X3))|X2=k2_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.37/0.56  fof(c_0_65, negated_conjecture, (v1_relat_1(esk7_0)&(v1_relat_1(esk8_0)&(r1_tarski(esk7_0,esk8_0)&~r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).
% 0.37/0.56  fof(c_0_66, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.37/0.56  fof(c_0_67, plain, ![X58, X59]:(~v1_relat_1(X58)|(~v1_relat_1(X59)|r1_tarski(k6_subset_1(k1_relat_1(X58),k1_relat_1(X59)),k1_relat_1(k6_subset_1(X58,X59))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).
% 0.37/0.56  fof(c_0_68, plain, ![X42, X43]:k6_subset_1(X42,X43)=k4_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.37/0.56  cnf(c_0_69, plain, (X1!=k1_relat_1(X2)|X2!=k1_xboole_0|~r2_hidden(X3,X1)|~r1_xboole_0(X4,X5)), inference(spm,[status(thm)],[c_0_57, c_0_33])).
% 0.37/0.56  cnf(c_0_70, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.37/0.56  cnf(c_0_71, plain, (k3_relat_1(X1)=k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_60, c_0_59])).
% 0.37/0.56  cnf(c_0_72, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.37/0.56  cnf(c_0_73, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_62, c_0_59])).
% 0.37/0.56  cnf(c_0_74, plain, (k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.37/0.56  cnf(c_0_75, plain, (X2=k3_tarski(k1_enumset1(X1,X1,X3))|r1_tarski(X1,esk3_3(X1,X2,X3))|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_64, c_0_59])).
% 0.37/0.56  cnf(c_0_76, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.37/0.56  cnf(c_0_77, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.37/0.56  fof(c_0_78, plain, ![X27, X28, X29]:(~r1_tarski(k4_xboole_0(X27,X28),X29)|r1_tarski(X27,k2_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.37/0.56  cnf(c_0_79, plain, (r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.37/0.56  cnf(c_0_80, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.37/0.56  cnf(c_0_81, plain, (X1=k1_xboole_0|X1!=k1_relat_1(X2)|X2!=k1_xboole_0|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_69, c_0_34])).
% 0.37/0.56  cnf(c_0_82, negated_conjecture, (~r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.37/0.56  cnf(c_0_83, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.37/0.56  cnf(c_0_84, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.37/0.56  cnf(c_0_85, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_59])).
% 0.37/0.56  cnf(c_0_86, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1)))), inference(spm,[status(thm)],[c_0_73, c_0_38])).
% 0.37/0.56  cnf(c_0_87, plain, (k2_relat_1(k3_tarski(k1_enumset1(X1,X1,X2)))=k3_tarski(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_59]), c_0_59])).
% 0.37/0.56  cnf(c_0_88, negated_conjecture, (k3_tarski(k1_enumset1(X1,X1,esk7_0))=esk8_0|r1_tarski(X1,esk3_3(X1,esk8_0,esk7_0))|~r1_tarski(X1,esk8_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.37/0.56  cnf(c_0_89, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_77])).
% 0.37/0.56  cnf(c_0_90, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.37/0.56  cnf(c_0_91, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.37/0.56  cnf(c_0_92, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_80])).
% 0.37/0.56  cnf(c_0_93, plain, (X1=k1_xboole_0|X1!=k1_relat_1(X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_48])).
% 0.37/0.56  fof(c_0_94, plain, ![X22]:r1_tarski(k1_xboole_0,X22), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.37/0.56  cnf(c_0_95, negated_conjecture, (~r1_tarski(k2_relat_1(esk7_0),k3_relat_1(esk8_0))|~r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])])).
% 0.37/0.56  cnf(c_0_96, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_85, c_0_71])).
% 0.37/0.56  cnf(c_0_97, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.37/0.56  cnf(c_0_98, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(k3_tarski(k1_enumset1(X2,X2,X1))))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.37/0.56  cnf(c_0_99, negated_conjecture, (k3_tarski(k1_enumset1(esk8_0,esk8_0,esk7_0))=esk8_0|r1_tarski(esk8_0,esk3_3(esk8_0,esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.37/0.56  cnf(c_0_100, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_90, c_0_59])).
% 0.37/0.56  cnf(c_0_101, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.37/0.56  cnf(c_0_102, plain, (k1_relat_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(er,[status(thm)],[c_0_93])).
% 0.37/0.56  cnf(c_0_103, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.37/0.56  cnf(c_0_104, negated_conjecture, (~r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0))|~r1_tarski(k2_relat_1(esk7_0),k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97])])).
% 0.37/0.56  cnf(c_0_105, negated_conjecture, (r1_tarski(esk8_0,esk3_3(esk8_0,esk8_0,esk7_0))|r1_tarski(k2_relat_1(esk7_0),k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_84]), c_0_97])])).
% 0.37/0.56  cnf(c_0_106, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_100, c_0_71])).
% 0.37/0.56  cnf(c_0_107, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_xboole_0|k4_xboole_0(X1,X2)!=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103])])).
% 0.37/0.56  cnf(c_0_108, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk3_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.37/0.56  cnf(c_0_109, negated_conjecture, (r1_tarski(esk8_0,esk3_3(esk8_0,esk8_0,esk7_0))|~r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.37/0.56  cnf(c_0_110, plain, (r1_tarski(k1_relat_1(X1),k3_relat_1(X2))|k4_xboole_0(X1,X2)!=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_103])])).
% 0.37/0.56  fof(c_0_111, plain, ![X24, X25, X26]:(~r1_tarski(X24,k2_xboole_0(X25,X26))|r1_tarski(k4_xboole_0(X24,X25),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.37/0.56  cnf(c_0_112, plain, (X1=k3_tarski(k1_enumset1(X2,X2,X3))|~r1_tarski(X3,X1)|~r1_tarski(X2,X1)|~r1_tarski(X1,esk3_3(X2,X1,X3))), inference(rw,[status(thm)],[c_0_108, c_0_59])).
% 0.37/0.56  cnf(c_0_113, negated_conjecture, (r1_tarski(esk8_0,esk3_3(esk8_0,esk8_0,esk7_0))|k4_xboole_0(esk7_0,esk8_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_97]), c_0_84])])).
% 0.37/0.56  cnf(c_0_114, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_111])).
% 0.37/0.56  cnf(c_0_115, negated_conjecture, (k3_tarski(k1_enumset1(esk8_0,esk8_0,esk7_0))=esk8_0|k4_xboole_0(esk7_0,esk8_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_76]), c_0_89])])).
% 0.37/0.56  cnf(c_0_116, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_114, c_0_59])).
% 0.37/0.56  cnf(c_0_117, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),k2_relat_1(esk8_0))|k4_xboole_0(esk7_0,esk8_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_115]), c_0_84]), c_0_97])])).
% 0.37/0.56  fof(c_0_118, plain, ![X23]:(~r1_tarski(X23,k1_xboole_0)|X23=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.37/0.56  cnf(c_0_119, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))), inference(spm,[status(thm)],[c_0_116, c_0_38])).
% 0.37/0.56  cnf(c_0_120, negated_conjecture, (k4_xboole_0(esk7_0,esk8_0)!=k1_xboole_0|~r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_117])).
% 0.37/0.56  cnf(c_0_121, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_118])).
% 0.37/0.56  cnf(c_0_122, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_119, c_0_85])).
% 0.37/0.56  cnf(c_0_123, negated_conjecture, (k4_xboole_0(esk7_0,esk8_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_110]), c_0_97]), c_0_84])])).
% 0.37/0.56  cnf(c_0_124, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 0.37/0.56  cnf(c_0_125, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_76])]), ['proof']).
% 0.37/0.56  # SZS output end CNFRefutation
% 0.37/0.56  # Proof object total steps             : 126
% 0.37/0.56  # Proof object clause steps            : 81
% 0.37/0.56  # Proof object formula steps           : 45
% 0.37/0.56  # Proof object conjectures             : 19
% 0.37/0.56  # Proof object clause conjectures      : 16
% 0.37/0.56  # Proof object formula conjectures     : 3
% 0.37/0.56  # Proof object initial clauses used    : 28
% 0.37/0.56  # Proof object initial formulas used   : 22
% 0.37/0.56  # Proof object generating inferences   : 36
% 0.37/0.56  # Proof object simplifying inferences  : 45
% 0.37/0.56  # Training examples: 0 positive, 0 negative
% 0.37/0.56  # Parsed axioms                        : 22
% 0.37/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.56  # Initial clauses                      : 33
% 0.37/0.56  # Removed in clause preprocessing      : 4
% 0.37/0.56  # Initial clauses in saturation        : 29
% 0.37/0.56  # Processed clauses                    : 1187
% 0.37/0.56  # ...of these trivial                  : 5
% 0.37/0.56  # ...subsumed                          : 706
% 0.37/0.56  # ...remaining for further processing  : 476
% 0.37/0.56  # Other redundant clauses eliminated   : 2
% 0.37/0.56  # Clauses deleted for lack of memory   : 0
% 0.37/0.56  # Backward-subsumed                    : 32
% 0.37/0.56  # Backward-rewritten                   : 9
% 0.37/0.56  # Generated clauses                    : 9170
% 0.37/0.56  # ...of the previous two non-trivial   : 8431
% 0.37/0.56  # Contextual simplify-reflections      : 4
% 0.37/0.56  # Paramodulations                      : 9146
% 0.37/0.56  # Factorizations                       : 6
% 0.37/0.56  # Equation resolutions                 : 18
% 0.37/0.56  # Propositional unsat checks           : 0
% 0.37/0.56  #    Propositional check models        : 0
% 0.37/0.56  #    Propositional check unsatisfiable : 0
% 0.37/0.56  #    Propositional clauses             : 0
% 0.37/0.56  #    Propositional clauses after purity: 0
% 0.37/0.56  #    Propositional unsat core size     : 0
% 0.37/0.56  #    Propositional preprocessing time  : 0.000
% 0.37/0.56  #    Propositional encoding time       : 0.000
% 0.37/0.56  #    Propositional solver time         : 0.000
% 0.37/0.56  #    Success case prop preproc time    : 0.000
% 0.37/0.56  #    Success case prop encoding time   : 0.000
% 0.37/0.56  #    Success case prop solver time     : 0.000
% 0.37/0.56  # Current number of processed clauses  : 433
% 0.37/0.56  #    Positive orientable unit clauses  : 17
% 0.37/0.56  #    Positive unorientable unit clauses: 1
% 0.37/0.56  #    Negative unit clauses             : 8
% 0.37/0.56  #    Non-unit-clauses                  : 407
% 0.37/0.56  # Current number of unprocessed clauses: 7215
% 0.37/0.56  # ...number of literals in the above   : 30766
% 0.37/0.56  # Current number of archived formulas  : 0
% 0.37/0.56  # Current number of archived clauses   : 45
% 0.37/0.56  # Clause-clause subsumption calls (NU) : 37909
% 0.37/0.56  # Rec. Clause-clause subsumption calls : 16356
% 0.37/0.56  # Non-unit clause-clause subsumptions  : 568
% 0.37/0.56  # Unit Clause-clause subsumption calls : 1315
% 0.37/0.56  # Rewrite failures with RHS unbound    : 0
% 0.37/0.56  # BW rewrite match attempts            : 59
% 0.37/0.56  # BW rewrite match successes           : 11
% 0.37/0.56  # Condensation attempts                : 0
% 0.37/0.56  # Condensation successes               : 0
% 0.37/0.56  # Termbank termtop insertions          : 152324
% 0.37/0.56  
% 0.37/0.56  # -------------------------------------------------
% 0.37/0.56  # User time                : 0.206 s
% 0.37/0.56  # System time              : 0.010 s
% 0.37/0.56  # Total time               : 0.216 s
% 0.37/0.56  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
