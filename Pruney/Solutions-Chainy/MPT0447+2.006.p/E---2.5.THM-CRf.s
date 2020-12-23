%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:22 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 478 expanded)
%              Number of clauses        :   68 ( 226 expanded)
%              Number of leaves         :   24 ( 122 expanded)
%              Depth                    :   13
%              Number of atoms          :  241 ( 868 expanded)
%              Number of equality atoms :   53 ( 336 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t28_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(t19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r2_hidden(X1,k2_relat_1(X2))
          & ! [X3] : ~ r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

fof(c_0_25,plain,(
    ! [X35,X36] : k3_tarski(k2_tarski(X35,X36)) = k2_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_28,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_relat_1(esk7_0)
    & r1_tarski(esk6_0,esk7_0)
    & ~ r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_29,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,k2_xboole_0(X21,X22))
      | r1_tarski(k4_xboole_0(X20,X21),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X29,X30] : k2_tarski(X29,X30) = k2_tarski(X30,X29) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X37,X38] : k2_xboole_0(k1_tarski(X37),X38) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_36,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | k2_xboole_0(k1_tarski(X33),X34) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(k4_xboole_0(X23,X24),X25)
      | r1_tarski(X23,k2_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_42,plain,(
    ! [X18,X19] : r1_tarski(k4_xboole_0(X18,X19),X18) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_43,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_44,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_46,plain,(
    ! [X42,X43,X44,X46,X47,X48,X49,X51] :
      ( ( ~ r2_hidden(X44,X43)
        | r2_hidden(k4_tarski(X44,esk2_3(X42,X43,X44)),X42)
        | X43 != k1_relat_1(X42) )
      & ( ~ r2_hidden(k4_tarski(X46,X47),X42)
        | r2_hidden(X46,X43)
        | X43 != k1_relat_1(X42) )
      & ( ~ r2_hidden(esk3_2(X48,X49),X49)
        | ~ r2_hidden(k4_tarski(esk3_2(X48,X49),X51),X48)
        | X49 = k1_relat_1(X48) )
      & ( r2_hidden(esk3_2(X48,X49),X49)
        | r2_hidden(k4_tarski(esk3_2(X48,X49),esk4_2(X48,X49)),X48)
        | X49 = k1_relat_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_47,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_31]),c_0_31])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r1_tarski(X2,esk6_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_41])).

cnf(c_0_51,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k3_tarski(k1_enumset1(k1_tarski(X1),k1_tarski(X1),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_54,plain,
    ( k3_tarski(k1_enumset1(k1_tarski(X1),k1_tarski(X1),X2)) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_38])).

cnf(c_0_55,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_56,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(X26,X27)
      | ~ r1_tarski(X28,X27)
      | r1_tarski(k2_xboole_0(X26,X28),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_57,plain,(
    ! [X53] :
      ( ~ v1_relat_1(X53)
      | k3_relat_1(X53) = k2_xboole_0(k1_relat_1(X53),k2_relat_1(X53)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_58,plain,(
    ! [X54,X55] :
      ( ~ v1_relat_1(X54)
      | ~ v1_relat_1(X55)
      | r1_tarski(k6_subset_1(k1_relat_1(X54),k1_relat_1(X55)),k1_relat_1(k6_subset_1(X54,X55))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).

fof(c_0_59,plain,(
    ! [X39,X40] : k6_subset_1(X39,X40) = k4_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_60,plain,(
    ! [X17] : r1_tarski(k1_xboole_0,X17) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_61,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_49,c_0_38])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r1_tarski(X1,k4_xboole_0(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_66,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_55])).

fof(c_0_67,plain,(
    ! [X5] :
      ( X5 = k1_xboole_0
      | r2_hidden(esk1_1(X5),X5) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_68,plain,(
    ! [X41] :
      ( ~ v1_xboole_0(X41)
      | v1_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_69,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_71,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | r1_tarski(X11,k2_xboole_0(X13,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_72,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_73,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_74,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_75,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_76,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk6_0,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_78,plain,(
    ! [X59,X60] :
      ( ~ v1_relat_1(X59)
      | ~ v1_relat_1(X60)
      | r1_tarski(k6_subset_1(k2_relat_1(X59),k2_relat_1(X60)),k2_relat_1(k6_subset_1(X59,X60))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).

fof(c_0_79,plain,(
    ! [X56,X57] :
      ( ~ v1_relat_1(X57)
      | ~ r2_hidden(X56,k2_relat_1(X57))
      | r2_hidden(esk5_2(X56,X57),k1_relat_1(X57)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_82,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_83,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_84,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_38])).

cnf(c_0_85,plain,
    ( k3_relat_1(X1) = k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_70,c_0_38])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_87,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_73])).

cnf(c_0_88,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_90,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_91,plain,
    ( r2_hidden(esk5_2(X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_92,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_93,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_95,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_96,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_86,c_0_38])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_87])).

cnf(c_0_99,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_100,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_101,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_73]),c_0_73])).

cnf(c_0_102,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])]),c_0_65])).

cnf(c_0_103,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk6_0),k3_relat_1(esk7_0))
    | ~ r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])])).

cnf(c_0_104,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_85])).

cnf(c_0_105,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_85])).

cnf(c_0_106,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk6_0),k1_relat_1(esk7_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_92]),c_0_100]),c_0_96]),c_0_92]),c_0_75])])).

fof(c_0_107,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(X9,X10) != k1_xboole_0
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | k4_xboole_0(X9,X10) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_108,plain,
    ( k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) = k2_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_101])).

cnf(c_0_109,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_81])).

cnf(c_0_110,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0))
    | ~ r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_100])])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_100]),c_0_75])])).

cnf(c_0_112,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( k4_xboole_0(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_99]),c_0_109]),c_0_100]),c_0_96]),c_0_109]),c_0_75])])).

cnf(c_0_114,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111])])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:11:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.028 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 0.19/0.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.45  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.45  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.19/0.45  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.45  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.19/0.45  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.19/0.45  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.19/0.45  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.45  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.19/0.45  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.19/0.45  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.19/0.45  fof(t15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 0.19/0.45  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.19/0.45  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.45  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.45  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.19/0.45  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.19/0.45  fof(t28_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 0.19/0.45  fof(t19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~((r2_hidden(X1,k2_relat_1(X2))&![X3]:~(r2_hidden(X3,k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 0.19/0.45  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.45  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.45  fof(c_0_24, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 0.19/0.45  fof(c_0_25, plain, ![X35, X36]:k3_tarski(k2_tarski(X35,X36))=k2_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.45  fof(c_0_26, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.45  fof(c_0_27, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_tarski(X15,X16)|r1_tarski(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.45  fof(c_0_28, negated_conjecture, (v1_relat_1(esk6_0)&(v1_relat_1(esk7_0)&(r1_tarski(esk6_0,esk7_0)&~r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.19/0.45  fof(c_0_29, plain, ![X20, X21, X22]:(~r1_tarski(X20,k2_xboole_0(X21,X22))|r1_tarski(k4_xboole_0(X20,X21),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.19/0.45  cnf(c_0_30, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.45  fof(c_0_32, plain, ![X29, X30]:k2_tarski(X29,X30)=k2_tarski(X30,X29), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.45  cnf(c_0_33, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.45  cnf(c_0_34, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.45  fof(c_0_35, plain, ![X37, X38]:k2_xboole_0(k1_tarski(X37),X38)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.19/0.45  fof(c_0_36, plain, ![X33, X34]:(~r2_hidden(X33,X34)|k2_xboole_0(k1_tarski(X33),X34)=X34), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.19/0.45  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.45  cnf(c_0_38, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.45  cnf(c_0_39, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.45  fof(c_0_40, plain, ![X23, X24, X25]:(~r1_tarski(k4_xboole_0(X23,X24),X25)|r1_tarski(X23,k2_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.19/0.45  cnf(c_0_41, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.45  fof(c_0_42, plain, ![X18, X19]:r1_tarski(k4_xboole_0(X18,X19),X18), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.45  fof(c_0_43, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.45  cnf(c_0_44, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.45  cnf(c_0_45, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.45  fof(c_0_46, plain, ![X42, X43, X44, X46, X47, X48, X49, X51]:(((~r2_hidden(X44,X43)|r2_hidden(k4_tarski(X44,esk2_3(X42,X43,X44)),X42)|X43!=k1_relat_1(X42))&(~r2_hidden(k4_tarski(X46,X47),X42)|r2_hidden(X46,X43)|X43!=k1_relat_1(X42)))&((~r2_hidden(esk3_2(X48,X49),X49)|~r2_hidden(k4_tarski(esk3_2(X48,X49),X51),X48)|X49=k1_relat_1(X48))&(r2_hidden(esk3_2(X48,X49),X49)|r2_hidden(k4_tarski(esk3_2(X48,X49),esk4_2(X48,X49)),X48)|X49=k1_relat_1(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.19/0.45  cnf(c_0_47, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.45  cnf(c_0_48, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_31]), c_0_31])).
% 0.19/0.45  cnf(c_0_49, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.45  cnf(c_0_50, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_tarski(X2,esk6_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_41])).
% 0.19/0.45  cnf(c_0_51, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.45  cnf(c_0_52, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.45  cnf(c_0_53, plain, (k3_tarski(k1_enumset1(k1_tarski(X1),k1_tarski(X1),X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_38])).
% 0.19/0.45  cnf(c_0_54, plain, (k3_tarski(k1_enumset1(k1_tarski(X1),k1_tarski(X1),X2))=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_38])).
% 0.19/0.45  cnf(c_0_55, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.45  fof(c_0_56, plain, ![X26, X27, X28]:(~r1_tarski(X26,X27)|~r1_tarski(X28,X27)|r1_tarski(k2_xboole_0(X26,X28),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.19/0.45  fof(c_0_57, plain, ![X53]:(~v1_relat_1(X53)|k3_relat_1(X53)=k2_xboole_0(k1_relat_1(X53),k2_relat_1(X53))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.19/0.45  fof(c_0_58, plain, ![X54, X55]:(~v1_relat_1(X54)|(~v1_relat_1(X55)|r1_tarski(k6_subset_1(k1_relat_1(X54),k1_relat_1(X55)),k1_relat_1(k6_subset_1(X54,X55))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).
% 0.19/0.45  fof(c_0_59, plain, ![X39, X40]:k6_subset_1(X39,X40)=k4_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.19/0.45  fof(c_0_60, plain, ![X17]:r1_tarski(k1_xboole_0,X17), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.45  cnf(c_0_61, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.45  cnf(c_0_62, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_49, c_0_38])).
% 0.19/0.45  cnf(c_0_63, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_tarski(X1,k4_xboole_0(esk6_0,X2))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.45  cnf(c_0_64, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_52])).
% 0.19/0.45  cnf(c_0_65, plain, (~r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54])])).
% 0.19/0.45  cnf(c_0_66, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_55])).
% 0.19/0.45  fof(c_0_67, plain, ![X5]:(X5=k1_xboole_0|r2_hidden(esk1_1(X5),X5)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.45  fof(c_0_68, plain, ![X41]:(~v1_xboole_0(X41)|v1_relat_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.19/0.45  cnf(c_0_69, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.45  cnf(c_0_70, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.45  fof(c_0_71, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|r1_tarski(X11,k2_xboole_0(X13,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.19/0.45  cnf(c_0_72, plain, (r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.45  cnf(c_0_73, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.45  cnf(c_0_74, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.45  cnf(c_0_75, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.45  cnf(c_0_76, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(k4_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.45  cnf(c_0_77, negated_conjecture, (r1_tarski(k4_xboole_0(esk6_0,X1),esk7_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.45  fof(c_0_78, plain, ![X59, X60]:(~v1_relat_1(X59)|(~v1_relat_1(X60)|r1_tarski(k6_subset_1(k2_relat_1(X59),k2_relat_1(X60)),k2_relat_1(k6_subset_1(X59,X60))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).
% 0.19/0.45  fof(c_0_79, plain, ![X56, X57]:(~v1_relat_1(X57)|(~r2_hidden(X56,k2_relat_1(X57))|r2_hidden(esk5_2(X56,X57),k1_relat_1(X57)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).
% 0.19/0.45  cnf(c_0_80, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.45  cnf(c_0_81, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.45  cnf(c_0_82, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.45  cnf(c_0_83, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.45  cnf(c_0_84, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_69, c_0_38])).
% 0.19/0.45  cnf(c_0_85, plain, (k3_relat_1(X1)=k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_70, c_0_38])).
% 0.19/0.45  cnf(c_0_86, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.45  cnf(c_0_87, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73]), c_0_73])).
% 0.19/0.45  cnf(c_0_88, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.45  cnf(c_0_89, negated_conjecture, (r1_tarski(k4_xboole_0(esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.45  cnf(c_0_90, plain, (r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.19/0.45  cnf(c_0_91, plain, (r2_hidden(esk5_2(X2,X1),k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.45  cnf(c_0_92, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.45  cnf(c_0_93, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.45  cnf(c_0_94, negated_conjecture, (~r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.45  cnf(c_0_95, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.45  cnf(c_0_96, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.45  cnf(c_0_97, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_86, c_0_38])).
% 0.19/0.45  cnf(c_0_98, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_74, c_0_87])).
% 0.19/0.45  cnf(c_0_99, negated_conjecture, (k4_xboole_0(esk6_0,esk7_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.45  cnf(c_0_100, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.45  cnf(c_0_101, plain, (r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_73]), c_0_73])).
% 0.19/0.45  cnf(c_0_102, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])]), c_0_65])).
% 0.19/0.45  cnf(c_0_103, negated_conjecture, (~r1_tarski(k2_relat_1(esk6_0),k3_relat_1(esk7_0))|~r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])])).
% 0.19/0.45  cnf(c_0_104, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_97, c_0_85])).
% 0.19/0.45  cnf(c_0_105, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_62, c_0_85])).
% 0.19/0.45  cnf(c_0_106, negated_conjecture, (k4_xboole_0(k1_relat_1(esk6_0),k1_relat_1(esk7_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_92]), c_0_100]), c_0_96]), c_0_92]), c_0_75])])).
% 0.19/0.45  fof(c_0_107, plain, ![X9, X10]:((k4_xboole_0(X9,X10)!=k1_xboole_0|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|k4_xboole_0(X9,X10)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.45  cnf(c_0_108, plain, (k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=k2_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), inference(spm,[status(thm)],[c_0_74, c_0_101])).
% 0.19/0.45  cnf(c_0_109, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_102, c_0_81])).
% 0.19/0.45  cnf(c_0_110, negated_conjecture, (~r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0))|~r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_100])])).
% 0.19/0.45  cnf(c_0_111, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_100]), c_0_75])])).
% 0.19/0.45  cnf(c_0_112, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.19/0.45  cnf(c_0_113, negated_conjecture, (k4_xboole_0(k2_relat_1(esk6_0),k2_relat_1(esk7_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_99]), c_0_109]), c_0_100]), c_0_96]), c_0_109]), c_0_75])])).
% 0.19/0.45  cnf(c_0_114, negated_conjecture, (~r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111])])).
% 0.19/0.45  cnf(c_0_115, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 116
% 0.19/0.45  # Proof object clause steps            : 68
% 0.19/0.45  # Proof object formula steps           : 48
% 0.19/0.45  # Proof object conjectures             : 20
% 0.19/0.45  # Proof object clause conjectures      : 17
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 28
% 0.19/0.45  # Proof object initial formulas used   : 24
% 0.19/0.45  # Proof object generating inferences   : 26
% 0.19/0.45  # Proof object simplifying inferences  : 42
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 24
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 33
% 0.19/0.45  # Removed in clause preprocessing      : 3
% 0.19/0.45  # Initial clauses in saturation        : 30
% 0.19/0.45  # Processed clauses                    : 1008
% 0.19/0.45  # ...of these trivial                  : 2
% 0.19/0.45  # ...subsumed                          : 639
% 0.19/0.45  # ...remaining for further processing  : 367
% 0.19/0.45  # Other redundant clauses eliminated   : 6
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 13
% 0.19/0.45  # Backward-rewritten                   : 13
% 0.19/0.45  # Generated clauses                    : 3561
% 0.19/0.45  # ...of the previous two non-trivial   : 3017
% 0.19/0.45  # Contextual simplify-reflections      : 1
% 0.19/0.45  # Paramodulations                      : 3553
% 0.19/0.45  # Factorizations                       : 2
% 0.19/0.45  # Equation resolutions                 : 6
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 308
% 0.19/0.45  #    Positive orientable unit clauses  : 27
% 0.19/0.45  #    Positive unorientable unit clauses: 1
% 0.19/0.45  #    Negative unit clauses             : 10
% 0.19/0.45  #    Non-unit-clauses                  : 270
% 0.19/0.45  # Current number of unprocessed clauses: 2052
% 0.19/0.45  # ...number of literals in the above   : 7810
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 58
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 17786
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 9376
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 450
% 0.19/0.45  # Unit Clause-clause subsumption calls : 611
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 30
% 0.19/0.45  # BW rewrite match successes           : 10
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 55958
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.108 s
% 0.19/0.45  # System time              : 0.005 s
% 0.19/0.45  # Total time               : 0.113 s
% 0.19/0.45  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
