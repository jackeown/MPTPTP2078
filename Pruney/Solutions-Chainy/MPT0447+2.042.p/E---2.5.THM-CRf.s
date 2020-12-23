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

% Result     : Theorem 5.03s
% Output     : CNFRefutation 5.03s
% Verified   : 
% Statistics : Number of formulae       :  149 (1774 expanded)
%              Number of clauses        :  104 ( 867 expanded)
%              Number of leaves         :   22 ( 448 expanded)
%              Depth                    :   22
%              Number of atoms          :  334 (3073 expanded)
%              Number of equality atoms :   79 (1324 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(t26_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(c_0_22,plain,(
    ! [X40,X41] : k3_tarski(k2_tarski(X40,X41)) = k2_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X33,X34] : r1_tarski(X33,k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X35,X36,X37] :
      ( ~ r1_tarski(X35,X36)
      | ~ r1_tarski(X37,X36)
      | r1_tarski(k2_xboole_0(X35,X37),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_31,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | r1_tarski(X15,k2_xboole_0(X17,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X44,X45] : k1_setfam_1(k2_tarski(X44,X45)) = k3_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_29])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r1_xboole_0(X5,X6)
        | r2_hidden(esk1_2(X5,X6),k3_xboole_0(X5,X6)) )
      & ( ~ r2_hidden(X10,k3_xboole_0(X8,X9))
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_29])).

cnf(c_0_45,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_26])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_49,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(k4_xboole_0(X27,X28),X29)
      | r1_tarski(X27,k2_xboole_0(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_51,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

cnf(c_0_52,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_47])).

fof(c_0_54,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_55,plain,(
    ! [X32] : r1_xboole_0(X32,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k3_tarski(k1_enumset1(X3,X3,X4)),X2)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_50,c_0_44])).

fof(c_0_58,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_relat_1(esk8_0)
    & r1_tarski(esk7_0,esk8_0)
    & ~ r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_56,c_0_29])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_45])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_65,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,k2_xboole_0(X25,X26))
      | r1_tarski(k4_xboole_0(X24,X25),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

fof(c_0_67,plain,(
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

fof(c_0_68,plain,(
    ! [X57] :
      ( ~ v1_relat_1(X57)
      | k3_relat_1(X57) = k2_xboole_0(k1_relat_1(X57),k2_relat_1(X57)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_69,plain,(
    ! [X60,X61] :
      ( ~ v1_relat_1(X60)
      | ~ v1_relat_1(X61)
      | k2_relat_1(k2_xboole_0(X60,X61)) = k2_xboole_0(k2_relat_1(X60),k2_relat_1(X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_45])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r1_tarski(X2,esk7_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_60])).

cnf(c_0_74,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_40])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_40])).

cnf(c_0_79,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_72,c_0_29])).

cnf(c_0_80,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

fof(c_0_81,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_82,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_83,plain,
    ( k3_relat_1(X1) = k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_75,c_0_29])).

cnf(c_0_84,plain,
    ( k2_relat_1(k3_tarski(k1_enumset1(X1,X1,X2))) = k3_tarski(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_29]),c_0_29])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r1_tarski(k4_xboole_0(X1,esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X1),X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_40])).

fof(c_0_87,plain,(
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

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_89,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_90,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_82,c_0_47])).

cnf(c_0_91,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_79,c_0_44])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_83])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,k2_relat_1(k3_tarski(k1_enumset1(X2,X2,X3))))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_84])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk8_0,esk8_0,esk7_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_95,plain,
    ( X1 != k1_relat_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r2_hidden(X4,X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_74])).

cnf(c_0_96,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk3_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

fof(c_0_97,plain,(
    ! [X22] : r1_tarski(k1_xboole_0,X22) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_98,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_99,plain,
    ( r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_90,c_0_53])).

cnf(c_0_100,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_89])).

cnf(c_0_101,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X4))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_91])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,k3_relat_1(k3_tarski(k1_enumset1(X2,X2,X3))))
    | ~ v1_relat_1(k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(k3_tarski(k1_enumset1(X2,X2,X3)))),k2_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_103,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk8_0,esk8_0,esk7_0)) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_94]),c_0_33])])).

cnf(c_0_104,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_105,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_106,plain,(
    ! [X58,X59] :
      ( ~ v1_relat_1(X58)
      | ~ v1_relat_1(X59)
      | r1_tarski(k6_subset_1(k1_relat_1(X58),k1_relat_1(X59)),k1_relat_1(k6_subset_1(X58,X59))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).

fof(c_0_107,plain,(
    ! [X42,X43] : k6_subset_1(X42,X43) = k4_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_108,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k4_xboole_0(X2,k4_xboole_0(X2,X3))))
    | ~ r1_xboole_0(X2,X3) ),
    inference(er,[status(thm)],[c_0_95])).

cnf(c_0_109,plain,
    ( X1 = k3_tarski(k1_enumset1(X2,X2,X3))
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,esk3_3(X2,X1,X3)) ),
    inference(rw,[status(thm)],[c_0_96,c_0_29])).

cnf(c_0_110,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_111,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_89])).

cnf(c_0_112,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_80,c_0_98])).

cnf(c_0_113,plain,
    ( r2_hidden(esk1_2(X1,X1),X1)
    | r1_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_60])).

cnf(c_0_114,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X1),X3) ),
    inference(spm,[status(thm)],[c_0_101,c_0_33])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(X1,k3_relat_1(esk8_0))
    | ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(esk8_0)),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104]),c_0_105])])).

cnf(c_0_116,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_117,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_118,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r1_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_100]),c_0_60])).

cnf(c_0_119,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X3
    | ~ r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X3)
    | ~ r1_tarski(k4_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_62])).

cnf(c_0_120,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_121,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_111]),c_0_110])])).

cnf(c_0_122,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_123,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_124,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_83])).

cnf(c_0_125,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_114])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_100]),c_0_110])])).

cnf(c_0_127,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_117]),c_0_117])).

cnf(c_0_128,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_89])).

cnf(c_0_129,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_110])])).

cnf(c_0_130,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_100])).

cnf(c_0_131,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk7_0),k3_relat_1(esk8_0))
    | ~ r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_105])])).

cnf(c_0_132,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_125])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(X1,k3_relat_1(esk8_0))
    | ~ r1_tarski(X2,k1_relat_1(esk8_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_126])).

cnf(c_0_134,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_127])).

cnf(c_0_135,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_128,c_0_122])).

cnf(c_0_136,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_60]),c_0_110])])).

cnf(c_0_137,plain,
    ( r1_tarski(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_130]),c_0_110])])).

cnf(c_0_138,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_132])])).

cnf(c_0_139,negated_conjecture,
    ( r1_tarski(X1,k3_relat_1(esk8_0))
    | ~ r1_tarski(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_40])).

cnf(c_0_140,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_xboole_0
    | k4_xboole_0(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_110])])).

cnf(c_0_141,plain,
    ( k1_xboole_0 = X1
    | X2 != k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_142,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_45])).

cnf(c_0_143,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk7_0),k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_144,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | k4_xboole_0(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_140]),c_0_110])])).

cnf(c_0_145,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | X3 != k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_137])).

cnf(c_0_146,negated_conjecture,
    ( k4_xboole_0(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_104]),c_0_105])])).

cnf(c_0_147,negated_conjecture,
    ( X1 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_64]),c_0_146])).

cnf(c_0_148,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_100,c_0_147]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 5.03/5.19  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 5.03/5.19  # and selection function PSelectComplexExceptUniqMaxHorn.
% 5.03/5.19  #
% 5.03/5.19  # Preprocessing time       : 0.028 s
% 5.03/5.19  
% 5.03/5.19  # Proof found!
% 5.03/5.19  # SZS status Theorem
% 5.03/5.19  # SZS output start CNFRefutation
% 5.03/5.19  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.03/5.19  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.03/5.19  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.03/5.19  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.03/5.19  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.03/5.19  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.03/5.19  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.03/5.19  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.03/5.19  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.03/5.19  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.03/5.19  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 5.03/5.19  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.03/5.19  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.03/5.19  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.03/5.19  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 5.03/5.19  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 5.03/5.19  fof(t26_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 5.03/5.19  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.03/5.19  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 5.03/5.19  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.03/5.19  fof(t15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 5.03/5.19  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.03/5.19  fof(c_0_22, plain, ![X40, X41]:k3_tarski(k2_tarski(X40,X41))=k2_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 5.03/5.19  fof(c_0_23, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 5.03/5.19  fof(c_0_24, plain, ![X33, X34]:r1_tarski(X33,k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 5.03/5.19  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.03/5.19  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.03/5.19  fof(c_0_27, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 5.03/5.19  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.03/5.19  cnf(c_0_29, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 5.03/5.19  fof(c_0_30, plain, ![X35, X36, X37]:(~r1_tarski(X35,X36)|~r1_tarski(X37,X36)|r1_tarski(k2_xboole_0(X35,X37),X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 5.03/5.19  fof(c_0_31, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|r1_tarski(X15,k2_xboole_0(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 5.03/5.19  cnf(c_0_32, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 5.03/5.19  cnf(c_0_33, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 5.03/5.19  cnf(c_0_34, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 5.03/5.19  cnf(c_0_35, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 5.03/5.19  fof(c_0_36, plain, ![X44, X45]:k1_setfam_1(k2_tarski(X44,X45))=k3_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 5.03/5.19  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 5.03/5.19  cnf(c_0_38, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 5.03/5.19  cnf(c_0_39, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_34, c_0_29])).
% 5.03/5.19  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_35])).
% 5.03/5.19  fof(c_0_41, plain, ![X5, X6, X8, X9, X10]:((r1_xboole_0(X5,X6)|r2_hidden(esk1_2(X5,X6),k3_xboole_0(X5,X6)))&(~r2_hidden(X10,k3_xboole_0(X8,X9))|~r1_xboole_0(X8,X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 5.03/5.19  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 5.03/5.19  fof(c_0_43, plain, ![X30, X31]:k4_xboole_0(X30,k4_xboole_0(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 5.03/5.19  cnf(c_0_44, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_29])).
% 5.03/5.19  cnf(c_0_45, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 5.03/5.19  cnf(c_0_46, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.03/5.19  cnf(c_0_47, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_26])).
% 5.03/5.19  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.03/5.19  fof(c_0_49, plain, ![X27, X28, X29]:(~r1_tarski(k4_xboole_0(X27,X28),X29)|r1_tarski(X27,k2_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 5.03/5.19  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 5.03/5.19  fof(c_0_51, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 5.03/5.19  cnf(c_0_52, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 5.03/5.19  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[c_0_48, c_0_47])).
% 5.03/5.19  fof(c_0_54, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 5.03/5.19  fof(c_0_55, plain, ![X32]:r1_xboole_0(X32,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 5.03/5.19  cnf(c_0_56, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 5.03/5.19  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~r1_tarski(k3_tarski(k1_enumset1(X3,X3,X4)),X2)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_50, c_0_44])).
% 5.03/5.19  fof(c_0_58, negated_conjecture, (v1_relat_1(esk7_0)&(v1_relat_1(esk8_0)&(r1_tarski(esk7_0,esk8_0)&~r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).
% 5.03/5.19  cnf(c_0_59, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X2,X3)), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 5.03/5.19  cnf(c_0_60, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 5.03/5.19  cnf(c_0_61, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 5.03/5.19  cnf(c_0_62, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_56, c_0_29])).
% 5.03/5.19  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_57, c_0_45])).
% 5.03/5.19  cnf(c_0_64, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.03/5.19  fof(c_0_65, plain, ![X24, X25, X26]:(~r1_tarski(X24,k2_xboole_0(X25,X26))|r1_tarski(k4_xboole_0(X24,X25),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 5.03/5.19  cnf(c_0_66, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 5.03/5.19  fof(c_0_67, plain, ![X46, X47, X48, X50, X51, X52, X53, X55]:(((~r2_hidden(X48,X47)|r2_hidden(k4_tarski(X48,esk4_3(X46,X47,X48)),X46)|X47!=k1_relat_1(X46))&(~r2_hidden(k4_tarski(X50,X51),X46)|r2_hidden(X50,X47)|X47!=k1_relat_1(X46)))&((~r2_hidden(esk5_2(X52,X53),X53)|~r2_hidden(k4_tarski(esk5_2(X52,X53),X55),X52)|X53=k1_relat_1(X52))&(r2_hidden(esk5_2(X52,X53),X53)|r2_hidden(k4_tarski(esk5_2(X52,X53),esk6_2(X52,X53)),X52)|X53=k1_relat_1(X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 5.03/5.19  fof(c_0_68, plain, ![X57]:(~v1_relat_1(X57)|k3_relat_1(X57)=k2_xboole_0(k1_relat_1(X57),k2_relat_1(X57))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 5.03/5.19  fof(c_0_69, plain, ![X60, X61]:(~v1_relat_1(X60)|(~v1_relat_1(X61)|k2_relat_1(k2_xboole_0(X60,X61))=k2_xboole_0(k2_relat_1(X60),k2_relat_1(X61)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).
% 5.03/5.19  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_62, c_0_45])).
% 5.03/5.19  cnf(c_0_71, negated_conjecture, (r1_tarski(X1,esk8_0)|~r1_tarski(X2,esk7_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 5.03/5.19  cnf(c_0_72, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 5.03/5.19  cnf(c_0_73, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_60])).
% 5.03/5.19  cnf(c_0_74, plain, (r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 5.03/5.19  cnf(c_0_75, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 5.03/5.19  cnf(c_0_76, plain, (k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 5.03/5.19  cnf(c_0_77, plain, (r1_tarski(X1,X2)|~r1_tarski(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_70, c_0_40])).
% 5.03/5.19  cnf(c_0_78, negated_conjecture, (r1_tarski(X1,esk8_0)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_71, c_0_40])).
% 5.03/5.19  cnf(c_0_79, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_72, c_0_29])).
% 5.03/5.19  cnf(c_0_80, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 5.03/5.19  fof(c_0_81, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 5.03/5.19  cnf(c_0_82, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.03/5.19  cnf(c_0_83, plain, (k3_relat_1(X1)=k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_75, c_0_29])).
% 5.03/5.19  cnf(c_0_84, plain, (k2_relat_1(k3_tarski(k1_enumset1(X1,X1,X2)))=k3_tarski(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_29]), c_0_29])).
% 5.03/5.19  cnf(c_0_85, negated_conjecture, (r1_tarski(X1,esk8_0)|~r1_tarski(k4_xboole_0(X1,esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 5.03/5.19  cnf(c_0_86, plain, (r1_tarski(k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X1),X2)), inference(spm,[status(thm)],[c_0_79, c_0_40])).
% 5.03/5.19  fof(c_0_87, plain, ![X18, X19, X20]:(((r1_tarski(X18,esk3_3(X18,X19,X20))|(~r1_tarski(X18,X19)|~r1_tarski(X20,X19))|X19=k2_xboole_0(X18,X20))&(r1_tarski(X20,esk3_3(X18,X19,X20))|(~r1_tarski(X18,X19)|~r1_tarski(X20,X19))|X19=k2_xboole_0(X18,X20)))&(~r1_tarski(X19,esk3_3(X18,X19,X20))|(~r1_tarski(X18,X19)|~r1_tarski(X20,X19))|X19=k2_xboole_0(X18,X20))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 5.03/5.19  cnf(c_0_88, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_80])).
% 5.03/5.19  cnf(c_0_89, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 5.03/5.19  cnf(c_0_90, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_82, c_0_47])).
% 5.03/5.19  cnf(c_0_91, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_79, c_0_44])).
% 5.03/5.19  cnf(c_0_92, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_62, c_0_83])).
% 5.03/5.19  cnf(c_0_93, plain, (r1_tarski(X1,k2_relat_1(k3_tarski(k1_enumset1(X2,X2,X3))))|~v1_relat_1(X3)|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X3))), inference(spm,[status(thm)],[c_0_44, c_0_84])).
% 5.03/5.19  cnf(c_0_94, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk8_0,esk8_0,esk7_0)),esk8_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 5.03/5.19  cnf(c_0_95, plain, (X1!=k1_relat_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r2_hidden(X4,X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_59, c_0_74])).
% 5.03/5.19  cnf(c_0_96, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk3_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 5.03/5.19  fof(c_0_97, plain, ![X22]:r1_tarski(k1_xboole_0,X22), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 5.03/5.19  cnf(c_0_98, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 5.03/5.19  cnf(c_0_99, plain, (r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))|r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_90, c_0_53])).
% 5.03/5.19  cnf(c_0_100, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_89])).
% 5.03/5.19  cnf(c_0_101, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4)|~r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X4)))), inference(spm,[status(thm)],[c_0_79, c_0_91])).
% 5.03/5.19  cnf(c_0_102, plain, (r1_tarski(X1,k3_relat_1(k3_tarski(k1_enumset1(X2,X2,X3))))|~v1_relat_1(k3_tarski(k1_enumset1(X2,X2,X3)))|~v1_relat_1(X3)|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k1_relat_1(k3_tarski(k1_enumset1(X2,X2,X3)))),k2_relat_1(X3))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 5.03/5.19  cnf(c_0_103, negated_conjecture, (k3_tarski(k1_enumset1(esk8_0,esk8_0,esk7_0))=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_94]), c_0_33])])).
% 5.03/5.19  cnf(c_0_104, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.03/5.19  cnf(c_0_105, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.03/5.19  fof(c_0_106, plain, ![X58, X59]:(~v1_relat_1(X58)|(~v1_relat_1(X59)|r1_tarski(k6_subset_1(k1_relat_1(X58),k1_relat_1(X59)),k1_relat_1(k6_subset_1(X58,X59))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).
% 5.03/5.19  fof(c_0_107, plain, ![X42, X43]:k6_subset_1(X42,X43)=k4_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 5.03/5.19  cnf(c_0_108, plain, (~r2_hidden(X1,k1_relat_1(k4_xboole_0(X2,k4_xboole_0(X2,X3))))|~r1_xboole_0(X2,X3)), inference(er,[status(thm)],[c_0_95])).
% 5.03/5.19  cnf(c_0_109, plain, (X1=k3_tarski(k1_enumset1(X2,X2,X3))|~r1_tarski(X3,X1)|~r1_tarski(X2,X1)|~r1_tarski(X1,esk3_3(X2,X1,X3))), inference(rw,[status(thm)],[c_0_96, c_0_29])).
% 5.03/5.19  cnf(c_0_110, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 5.03/5.19  cnf(c_0_111, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_59, c_0_89])).
% 5.03/5.19  cnf(c_0_112, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_80, c_0_98])).
% 5.03/5.19  cnf(c_0_113, plain, (r2_hidden(esk1_2(X1,X1),X1)|r1_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_60])).
% 5.03/5.19  cnf(c_0_114, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X1),X3)), inference(spm,[status(thm)],[c_0_101, c_0_33])).
% 5.03/5.19  cnf(c_0_115, negated_conjecture, (r1_tarski(X1,k3_relat_1(esk8_0))|~r1_tarski(k4_xboole_0(X1,k1_relat_1(esk8_0)),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104]), c_0_105])])).
% 5.03/5.19  cnf(c_0_116, plain, (r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 5.03/5.19  cnf(c_0_117, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 5.03/5.19  cnf(c_0_118, plain, (~r2_hidden(X1,k1_relat_1(X2))|~r1_xboole_0(X2,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_100]), c_0_60])).
% 5.03/5.19  cnf(c_0_119, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X3|~r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X3)|~r1_tarski(k4_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_32, c_0_62])).
% 5.03/5.19  cnf(c_0_120, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k1_xboole_0|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 5.03/5.19  cnf(c_0_121, plain, (r1_tarski(X1,k4_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_111]), c_0_110])])).
% 5.03/5.19  cnf(c_0_122, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 5.03/5.19  cnf(c_0_123, negated_conjecture, (~r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.03/5.19  cnf(c_0_124, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_39, c_0_83])).
% 5.03/5.19  cnf(c_0_125, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_77, c_0_114])).
% 5.03/5.19  cnf(c_0_126, negated_conjecture, (r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_100]), c_0_110])])).
% 5.03/5.19  cnf(c_0_127, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_117]), c_0_117])).
% 5.03/5.19  cnf(c_0_128, plain, (k1_relat_1(X1)=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_118, c_0_89])).
% 5.03/5.19  cnf(c_0_129, plain, (k1_xboole_0=X1|~r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_110])])).
% 5.03/5.19  cnf(c_0_130, plain, (r1_tarski(X1,k1_xboole_0)|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_100])).
% 5.03/5.19  cnf(c_0_131, negated_conjecture, (~r1_tarski(k2_relat_1(esk7_0),k3_relat_1(esk8_0))|~r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_105])])).
% 5.03/5.19  cnf(c_0_132, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_115, c_0_125])).
% 5.03/5.19  cnf(c_0_133, negated_conjecture, (r1_tarski(X1,k3_relat_1(esk8_0))|~r1_tarski(X2,k1_relat_1(esk8_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_63, c_0_126])).
% 5.03/5.19  cnf(c_0_134, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_32, c_0_127])).
% 5.03/5.19  cnf(c_0_135, plain, (k1_relat_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_128, c_0_122])).
% 5.03/5.19  cnf(c_0_136, plain, (k1_xboole_0=X1|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_60]), c_0_110])])).
% 5.03/5.19  cnf(c_0_137, plain, (r1_tarski(X1,X2)|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_130]), c_0_110])])).
% 5.03/5.19  cnf(c_0_138, negated_conjecture, (~r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_132])])).
% 5.03/5.19  cnf(c_0_139, negated_conjecture, (r1_tarski(X1,k3_relat_1(esk8_0))|~r1_tarski(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_133, c_0_40])).
% 5.03/5.19  cnf(c_0_140, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_xboole_0|k4_xboole_0(X1,X2)!=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_110])])).
% 5.03/5.19  cnf(c_0_141, plain, (k1_xboole_0=X1|X2!=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_136, c_0_137])).
% 5.03/5.19  cnf(c_0_142, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_79, c_0_45])).
% 5.03/5.19  cnf(c_0_143, negated_conjecture, (~r1_tarski(k1_relat_1(esk7_0),k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 5.03/5.19  cnf(c_0_144, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|k4_xboole_0(X1,X2)!=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_140]), c_0_110])])).
% 5.03/5.19  cnf(c_0_145, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|X3!=k1_xboole_0|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_137])).
% 5.03/5.19  cnf(c_0_146, negated_conjecture, (k4_xboole_0(esk7_0,esk8_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_104]), c_0_105])])).
% 5.03/5.19  cnf(c_0_147, negated_conjecture, (X1!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_64]), c_0_146])).
% 5.03/5.19  cnf(c_0_148, plain, ($false), inference(sr,[status(thm)],[c_0_100, c_0_147]), ['proof']).
% 5.03/5.19  # SZS output end CNFRefutation
% 5.03/5.19  # Proof object total steps             : 149
% 5.03/5.19  # Proof object clause steps            : 104
% 5.03/5.19  # Proof object formula steps           : 45
% 5.03/5.19  # Proof object conjectures             : 22
% 5.03/5.19  # Proof object clause conjectures      : 19
% 5.03/5.19  # Proof object formula conjectures     : 3
% 5.03/5.19  # Proof object initial clauses used    : 27
% 5.03/5.19  # Proof object initial formulas used   : 22
% 5.03/5.19  # Proof object generating inferences   : 57
% 5.03/5.19  # Proof object simplifying inferences  : 56
% 5.03/5.19  # Training examples: 0 positive, 0 negative
% 5.03/5.19  # Parsed axioms                        : 22
% 5.03/5.19  # Removed by relevancy pruning/SinE    : 0
% 5.03/5.19  # Initial clauses                      : 33
% 5.03/5.19  # Removed in clause preprocessing      : 4
% 5.03/5.19  # Initial clauses in saturation        : 29
% 5.03/5.19  # Processed clauses                    : 11958
% 5.03/5.19  # ...of these trivial                  : 134
% 5.03/5.19  # ...subsumed                          : 8961
% 5.03/5.19  # ...remaining for further processing  : 2863
% 5.03/5.19  # Other redundant clauses eliminated   : 2
% 5.03/5.19  # Clauses deleted for lack of memory   : 0
% 5.03/5.19  # Backward-subsumed                    : 202
% 5.03/5.19  # Backward-rewritten                   : 367
% 5.03/5.19  # Generated clauses                    : 343817
% 5.03/5.19  # ...of the previous two non-trivial   : 319128
% 5.03/5.19  # Contextual simplify-reflections      : 71
% 5.03/5.19  # Paramodulations                      : 343728
% 5.03/5.19  # Factorizations                       : 10
% 5.03/5.19  # Equation resolutions                 : 73
% 5.03/5.19  # Propositional unsat checks           : 0
% 5.03/5.19  #    Propositional check models        : 0
% 5.03/5.19  #    Propositional check unsatisfiable : 0
% 5.03/5.19  #    Propositional clauses             : 0
% 5.03/5.19  #    Propositional clauses after purity: 0
% 5.03/5.19  #    Propositional unsat core size     : 0
% 5.03/5.19  #    Propositional preprocessing time  : 0.000
% 5.03/5.19  #    Propositional encoding time       : 0.000
% 5.03/5.19  #    Propositional solver time         : 0.000
% 5.03/5.19  #    Success case prop preproc time    : 0.000
% 5.03/5.19  #    Success case prop encoding time   : 0.000
% 5.03/5.19  #    Success case prop solver time     : 0.000
% 5.03/5.19  # Current number of processed clauses  : 2286
% 5.03/5.19  #    Positive orientable unit clauses  : 57
% 5.03/5.19  #    Positive unorientable unit clauses: 0
% 5.03/5.19  #    Negative unit clauses             : 17
% 5.03/5.19  #    Non-unit-clauses                  : 2212
% 5.03/5.19  # Current number of unprocessed clauses: 305944
% 5.03/5.19  # ...number of literals in the above   : 1266534
% 5.03/5.19  # Current number of archived formulas  : 0
% 5.03/5.19  # Current number of archived clauses   : 579
% 5.03/5.19  # Clause-clause subsumption calls (NU) : 1270094
% 5.03/5.19  # Rec. Clause-clause subsumption calls : 552873
% 5.03/5.19  # Non-unit clause-clause subsumptions  : 6091
% 5.03/5.19  # Unit Clause-clause subsumption calls : 10891
% 5.03/5.19  # Rewrite failures with RHS unbound    : 0
% 5.03/5.19  # BW rewrite match attempts            : 3566
% 5.03/5.19  # BW rewrite match successes           : 94
% 5.03/5.19  # Condensation attempts                : 0
% 5.03/5.19  # Condensation successes               : 0
% 5.03/5.19  # Termbank termtop insertions          : 7758540
% 5.03/5.21  
% 5.03/5.21  # -------------------------------------------------
% 5.03/5.21  # User time                : 4.694 s
% 5.03/5.21  # System time              : 0.178 s
% 5.03/5.21  # Total time               : 4.873 s
% 5.03/5.21  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
