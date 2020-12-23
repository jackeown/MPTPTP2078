%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:22 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 760 expanded)
%              Number of clauses        :   87 ( 342 expanded)
%              Number of leaves         :   32 ( 205 expanded)
%              Depth                    :   14
%              Number of atoms          :  310 (1405 expanded)
%              Number of equality atoms :   70 ( 532 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

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

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t9_tarski,axiom,(
    ! [X1] :
    ? [X2] :
      ( r2_hidden(X1,X2)
      & ! [X3,X4] :
          ( ( r2_hidden(X3,X2)
            & r1_tarski(X4,X3) )
         => r2_hidden(X4,X2) )
      & ! [X3] :
          ~ ( r2_hidden(X3,X2)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & ! [X5] :
                      ( r1_tarski(X5,X3)
                     => r2_hidden(X5,X4) ) ) )
      & ! [X3] :
          ~ ( r1_tarski(X3,X2)
            & ~ r2_tarski(X3,X2)
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tarski)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

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

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

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

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r2_hidden(X1,k2_relat_1(X2))
          & ! [X3] : ~ r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(c_0_32,plain,(
    ! [X54,X55] : k3_tarski(k2_tarski(X54,X55)) = k2_xboole_0(X54,X55) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_33,plain,(
    ! [X49,X50] : k1_enumset1(X49,X49,X50) = k2_tarski(X49,X50) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_34,plain,(
    ! [X36,X37,X38] :
      ( ~ r1_tarski(k4_xboole_0(X36,X37),X38)
      | r1_tarski(X36,k2_xboole_0(X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_35,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_37,plain,(
    ! [X51,X52,X53] : k2_enumset1(X51,X51,X52,X53) = k1_enumset1(X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_38,plain,(
    ! [X14] : k2_xboole_0(X14,X14) = X14 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

fof(c_0_40,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_41,plain,(
    ! [X41] : r1_xboole_0(X41,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_46,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_tarski(X24,X25)
      | r1_tarski(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_47,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & v1_relat_1(esk11_0)
    & r1_tarski(esk10_0,esk11_0)
    & ~ r1_tarski(k3_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

fof(c_0_48,plain,(
    ! [X33,X34,X35] :
      ( ~ r1_tarski(X33,k2_xboole_0(X34,X35))
      | r1_tarski(k4_xboole_0(X33,X34),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_49,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(X21,X22)
        | X21 != X22 )
      & ( r1_tarski(X22,X21)
        | X21 != X22 )
      & ( ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X21)
        | X21 = X22 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_52,plain,(
    ! [X56,X57,X59] :
      ( ( r2_hidden(esk3_2(X56,X57),X57)
        | ~ r2_hidden(X56,X57) )
      & ( ~ r2_hidden(X59,X57)
        | ~ r2_hidden(X59,esk3_2(X56,X57))
        | ~ r2_hidden(X56,X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_54,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_43]),c_0_44])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk10_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_59,plain,(
    ! [X47,X48] : k2_tarski(X47,X48) = k2_tarski(X48,X47) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_60,plain,(
    ! [X42,X43] : r1_tarski(X42,k2_xboole_0(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_61,plain,(
    ! [X70,X71] : k1_setfam_1(k2_tarski(X70,X71)) = k3_xboole_0(X70,X71) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_63,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_64,plain,(
    ! [X60,X62,X63,X64,X66,X67] :
      ( r2_hidden(X60,esk4_1(X60))
      & ( ~ r2_hidden(X62,esk4_1(X60))
        | ~ r1_tarski(X63,X62)
        | r2_hidden(X63,esk4_1(X60)) )
      & ( r2_hidden(esk5_2(X60,X64),esk4_1(X60))
        | ~ r2_hidden(X64,esk4_1(X60)) )
      & ( ~ r1_tarski(X66,X64)
        | r2_hidden(X66,esk5_2(X60,X64))
        | ~ r2_hidden(X64,esk4_1(X60)) )
      & ( ~ r1_tarski(X67,esk4_1(X60))
        | r2_tarski(X67,esk4_1(X60))
        | r2_hidden(X67,esk4_1(X60)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_tarski])])])])])])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,esk11_0)
    | ~ r1_tarski(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_67,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_43]),c_0_44])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_71,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_72,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_73,plain,(
    ! [X39,X40] : k4_xboole_0(X39,k4_xboole_0(X39,X40)) = k3_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_74,plain,(
    ! [X26] : r1_tarski(k1_xboole_0,X26) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(esk3_2(X1,k1_xboole_0),X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_77,plain,(
    ! [X73,X74,X75,X77,X78,X79,X80,X82] :
      ( ( ~ r2_hidden(X75,X74)
        | r2_hidden(k4_tarski(X75,esk6_3(X73,X74,X75)),X73)
        | X74 != k1_relat_1(X73) )
      & ( ~ r2_hidden(k4_tarski(X77,X78),X73)
        | r2_hidden(X77,X74)
        | X74 != k1_relat_1(X73) )
      & ( ~ r2_hidden(esk7_2(X79,X80),X80)
        | ~ r2_hidden(k4_tarski(esk7_2(X79,X80),X82),X79)
        | X80 = k1_relat_1(X79) )
      & ( r2_hidden(esk7_2(X79,X80),X80)
        | r2_hidden(k4_tarski(esk7_2(X79,X80),esk8_2(X79,X80)),X79)
        | X80 = k1_relat_1(X79) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_78,plain,(
    ! [X30,X31,X32] : k4_xboole_0(k4_xboole_0(X30,X31),X32) = k4_xboole_0(X30,k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(X1,esk11_0)
    | ~ r1_tarski(k4_xboole_0(X1,esk11_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_80,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X1),X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_81,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_36]),c_0_36]),c_0_44]),c_0_44])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_43]),c_0_44])).

cnf(c_0_83,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_84,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_36])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_86,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_87,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_88,plain,(
    ! [X27,X28] : r1_tarski(k4_xboole_0(X27,X28),X27) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_90,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_91,plain,(
    ! [X72] :
      ( ~ v1_xboole_0(X72)
      | v1_relat_1(X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_92,plain,(
    ! [X85,X86] :
      ( ~ v1_relat_1(X85)
      | ~ v1_relat_1(X86)
      | r1_tarski(k6_subset_1(k1_relat_1(X85),k1_relat_1(X86)),k1_relat_1(k6_subset_1(X85,X86))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).

fof(c_0_93,plain,(
    ! [X68,X69] : k6_subset_1(X68,X69) = k4_xboole_0(X68,X69) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_94,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_enumset1(esk10_0,esk10_0,esk10_0,esk11_0)),esk11_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_81])).

cnf(c_0_97,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_setfam_1(k2_enumset1(X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84]),c_0_84]),c_0_44]),c_0_44])).

cnf(c_0_98,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_84]),c_0_44])).

fof(c_0_99,plain,(
    ! [X29] : k4_xboole_0(X29,k1_xboole_0) = X29 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_100,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_101,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_102,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

fof(c_0_103,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_104,plain,(
    ! [X87,X88] :
      ( ~ v1_relat_1(X88)
      | ~ r2_hidden(X87,k2_relat_1(X88))
      | r2_hidden(esk9_2(X87,X88),k1_relat_1(X88)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).

cnf(c_0_105,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_106,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_107,plain,(
    ! [X44,X45,X46] :
      ( ~ r1_tarski(X44,X45)
      | ~ r1_tarski(X46,X45)
      | r1_tarski(k2_xboole_0(X44,X46),X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_108,plain,(
    ! [X84] :
      ( ~ v1_relat_1(X84)
      | k3_relat_1(X84) = k2_xboole_0(k1_relat_1(X84),k2_relat_1(X84)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_109,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_110,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_111,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_43]),c_0_44])).

cnf(c_0_112,negated_conjecture,
    ( k3_tarski(k2_enumset1(esk10_0,esk10_0,esk10_0,esk11_0)) = esk11_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_95]),c_0_96])])).

cnf(c_0_113,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98]),c_0_98])).

cnf(c_0_114,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_115,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_116,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_102])).

cnf(c_0_117,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

fof(c_0_118,plain,(
    ! [X90,X91] :
      ( ~ v1_relat_1(X90)
      | ~ v1_relat_1(X91)
      | r1_tarski(k6_subset_1(k2_relat_1(X90),k2_relat_1(X91)),k2_relat_1(k6_subset_1(X90,X91))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).

cnf(c_0_119,plain,
    ( r2_hidden(esk9_2(X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_120,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_121,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_122,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_123,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110]),c_0_110])).

cnf(c_0_124,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk10_0),esk11_0) = k4_xboole_0(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_125,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115]),c_0_115])).

cnf(c_0_126,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_127,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_128,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_119]),c_0_120])])).

cnf(c_0_129,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_43]),c_0_44])).

cnf(c_0_130,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_43]),c_0_44])).

cnf(c_0_131,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_123])).

cnf(c_0_132,negated_conjecture,
    ( k4_xboole_0(esk10_0,esk11_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_115])).

cnf(c_0_133,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_126])).

cnf(c_0_134,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_135,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_136,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_110]),c_0_110])).

cnf(c_0_137,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_128,c_0_117])).

cnf(c_0_138,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_139,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_140,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_130])).

cnf(c_0_141,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk10_0),k1_relat_1(esk11_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_133]),c_0_134]),c_0_135]),c_0_133]),c_0_87])])).

cnf(c_0_142,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_81])).

cnf(c_0_143,plain,
    ( k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) = k2_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_136])).

cnf(c_0_144,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_137])).

cnf(c_0_145,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk10_0),k3_relat_1(esk11_0))
    | ~ r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_135])])).

cnf(c_0_146,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_134]),c_0_87])])).

cnf(c_0_147,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k2_relat_1(X2)),k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_130])).

cnf(c_0_148,negated_conjecture,
    ( k4_xboole_0(k2_relat_1(esk10_0),k2_relat_1(esk11_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_132]),c_0_144]),c_0_134]),c_0_135]),c_0_144]),c_0_87])])).

cnf(c_0_149,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_145,c_0_146])])).

cnf(c_0_150,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_148]),c_0_134]),c_0_87])]),c_0_149]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.54/1.77  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 1.54/1.77  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.54/1.77  #
% 1.54/1.77  # Preprocessing time       : 0.030 s
% 1.54/1.77  
% 1.54/1.77  # Proof found!
% 1.54/1.77  # SZS status Theorem
% 1.54/1.77  # SZS output start CNFRefutation
% 1.54/1.77  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.54/1.77  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.54/1.77  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.54/1.77  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.54/1.77  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.54/1.77  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 1.54/1.77  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.54/1.77  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.54/1.77  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.54/1.77  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.54/1.77  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.54/1.77  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 1.54/1.77  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.54/1.77  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.54/1.77  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.54/1.77  fof(t9_tarski, axiom, ![X1]:?[X2]:(((r2_hidden(X1,X2)&![X3, X4]:((r2_hidden(X3,X2)&r1_tarski(X4,X3))=>r2_hidden(X4,X2)))&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&![X5]:(r1_tarski(X5,X3)=>r2_hidden(X5,X4)))))))&![X3]:~(((r1_tarski(X3,X2)&~(r2_tarski(X3,X2)))&~(r2_hidden(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tarski)).
% 1.54/1.77  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.54/1.77  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.54/1.77  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.54/1.77  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.54/1.77  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.54/1.77  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.54/1.77  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.54/1.77  fof(t15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 1.54/1.77  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.54/1.77  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.54/1.77  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.54/1.77  fof(t19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~((r2_hidden(X1,k2_relat_1(X2))&![X3]:~(r2_hidden(X3,k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 1.54/1.77  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.54/1.77  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.54/1.77  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.54/1.77  fof(t28_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 1.54/1.77  fof(c_0_32, plain, ![X54, X55]:k3_tarski(k2_tarski(X54,X55))=k2_xboole_0(X54,X55), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.54/1.77  fof(c_0_33, plain, ![X49, X50]:k1_enumset1(X49,X49,X50)=k2_tarski(X49,X50), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.54/1.77  fof(c_0_34, plain, ![X36, X37, X38]:(~r1_tarski(k4_xboole_0(X36,X37),X38)|r1_tarski(X36,k2_xboole_0(X37,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 1.54/1.77  cnf(c_0_35, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.54/1.77  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.54/1.77  fof(c_0_37, plain, ![X51, X52, X53]:k2_enumset1(X51,X51,X52,X53)=k1_enumset1(X51,X52,X53), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.54/1.77  fof(c_0_38, plain, ![X14]:k2_xboole_0(X14,X14)=X14, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 1.54/1.77  fof(c_0_39, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 1.54/1.77  fof(c_0_40, plain, ![X15, X16, X18, X19, X20]:(((r2_hidden(esk2_2(X15,X16),X15)|r1_xboole_0(X15,X16))&(r2_hidden(esk2_2(X15,X16),X16)|r1_xboole_0(X15,X16)))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|~r1_xboole_0(X18,X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 1.54/1.77  fof(c_0_41, plain, ![X41]:r1_xboole_0(X41,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 1.54/1.77  cnf(c_0_42, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.54/1.77  cnf(c_0_43, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 1.54/1.77  cnf(c_0_44, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.54/1.77  cnf(c_0_45, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.54/1.77  fof(c_0_46, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_tarski(X24,X25)|r1_tarski(X23,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.54/1.77  fof(c_0_47, negated_conjecture, (v1_relat_1(esk10_0)&(v1_relat_1(esk11_0)&(r1_tarski(esk10_0,esk11_0)&~r1_tarski(k3_relat_1(esk10_0),k3_relat_1(esk11_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 1.54/1.77  fof(c_0_48, plain, ![X33, X34, X35]:(~r1_tarski(X33,k2_xboole_0(X34,X35))|r1_tarski(k4_xboole_0(X33,X34),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 1.54/1.77  fof(c_0_49, plain, ![X21, X22]:(((r1_tarski(X21,X22)|X21!=X22)&(r1_tarski(X22,X21)|X21!=X22))&(~r1_tarski(X21,X22)|~r1_tarski(X22,X21)|X21=X22)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.54/1.77  cnf(c_0_50, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.54/1.77  cnf(c_0_51, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.54/1.77  fof(c_0_52, plain, ![X56, X57, X59]:((r2_hidden(esk3_2(X56,X57),X57)|~r2_hidden(X56,X57))&(~r2_hidden(X59,X57)|~r2_hidden(X59,esk3_2(X56,X57))|~r2_hidden(X56,X57))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 1.54/1.77  cnf(c_0_53, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 1.54/1.77  cnf(c_0_54, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_43]), c_0_44])).
% 1.54/1.77  cnf(c_0_55, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.54/1.77  cnf(c_0_56, negated_conjecture, (r1_tarski(esk10_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.54/1.77  cnf(c_0_57, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.54/1.77  cnf(c_0_58, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.54/1.77  fof(c_0_59, plain, ![X47, X48]:k2_tarski(X47,X48)=k2_tarski(X48,X47), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.54/1.77  fof(c_0_60, plain, ![X42, X43]:r1_tarski(X42,k2_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.54/1.77  fof(c_0_61, plain, ![X70, X71]:k1_setfam_1(k2_tarski(X70,X71))=k3_xboole_0(X70,X71), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.54/1.77  cnf(c_0_62, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.54/1.77  cnf(c_0_63, plain, (r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.54/1.77  fof(c_0_64, plain, ![X60, X62, X63, X64, X66, X67]:(((r2_hidden(X60,esk4_1(X60))&(~r2_hidden(X62,esk4_1(X60))|~r1_tarski(X63,X62)|r2_hidden(X63,esk4_1(X60))))&((r2_hidden(esk5_2(X60,X64),esk4_1(X60))|~r2_hidden(X64,esk4_1(X60)))&(~r1_tarski(X66,X64)|r2_hidden(X66,esk5_2(X60,X64))|~r2_hidden(X64,esk4_1(X60)))))&(~r1_tarski(X67,esk4_1(X60))|r2_tarski(X67,esk4_1(X60))|r2_hidden(X67,esk4_1(X60)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_tarski])])])])])])).
% 1.54/1.77  cnf(c_0_65, plain, (r1_tarski(X1,X2)|~r1_tarski(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 1.54/1.77  cnf(c_0_66, negated_conjecture, (r1_tarski(X1,esk11_0)|~r1_tarski(X1,esk10_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.54/1.77  cnf(c_0_67, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_43]), c_0_44])).
% 1.54/1.77  cnf(c_0_68, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_58])).
% 1.54/1.77  cnf(c_0_69, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.54/1.77  cnf(c_0_70, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.54/1.77  fof(c_0_71, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.54/1.77  cnf(c_0_72, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.54/1.77  fof(c_0_73, plain, ![X39, X40]:k4_xboole_0(X39,k4_xboole_0(X39,X40))=k3_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.54/1.77  fof(c_0_74, plain, ![X26]:r1_tarski(k1_xboole_0,X26), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.54/1.77  cnf(c_0_75, plain, (~r2_hidden(esk3_2(X1,k1_xboole_0),X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 1.54/1.77  cnf(c_0_76, plain, (r2_hidden(X1,esk4_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 1.54/1.77  fof(c_0_77, plain, ![X73, X74, X75, X77, X78, X79, X80, X82]:(((~r2_hidden(X75,X74)|r2_hidden(k4_tarski(X75,esk6_3(X73,X74,X75)),X73)|X74!=k1_relat_1(X73))&(~r2_hidden(k4_tarski(X77,X78),X73)|r2_hidden(X77,X74)|X74!=k1_relat_1(X73)))&((~r2_hidden(esk7_2(X79,X80),X80)|~r2_hidden(k4_tarski(esk7_2(X79,X80),X82),X79)|X80=k1_relat_1(X79))&(r2_hidden(esk7_2(X79,X80),X80)|r2_hidden(k4_tarski(esk7_2(X79,X80),esk8_2(X79,X80)),X79)|X80=k1_relat_1(X79)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.54/1.77  fof(c_0_78, plain, ![X30, X31, X32]:k4_xboole_0(k4_xboole_0(X30,X31),X32)=k4_xboole_0(X30,k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.54/1.77  cnf(c_0_79, negated_conjecture, (r1_tarski(X1,esk11_0)|~r1_tarski(k4_xboole_0(X1,esk11_0),esk10_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.54/1.77  cnf(c_0_80, plain, (r1_tarski(k4_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X1),X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 1.54/1.77  cnf(c_0_81, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_36]), c_0_36]), c_0_44]), c_0_44])).
% 1.54/1.77  cnf(c_0_82, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_43]), c_0_44])).
% 1.54/1.77  cnf(c_0_83, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.54/1.77  cnf(c_0_84, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_36])).
% 1.54/1.77  cnf(c_0_85, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.54/1.77  cnf(c_0_86, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.54/1.77  cnf(c_0_87, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 1.54/1.77  fof(c_0_88, plain, ![X27, X28]:r1_tarski(k4_xboole_0(X27,X28),X27), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.54/1.77  cnf(c_0_89, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 1.54/1.77  cnf(c_0_90, plain, (r2_hidden(k4_tarski(X1,esk6_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.54/1.77  fof(c_0_91, plain, ![X72]:(~v1_xboole_0(X72)|v1_relat_1(X72)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 1.54/1.77  fof(c_0_92, plain, ![X85, X86]:(~v1_relat_1(X85)|(~v1_relat_1(X86)|r1_tarski(k6_subset_1(k1_relat_1(X85),k1_relat_1(X86)),k1_relat_1(k6_subset_1(X85,X86))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).
% 1.54/1.77  fof(c_0_93, plain, ![X68, X69]:k6_subset_1(X68,X69)=k4_xboole_0(X68,X69), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 1.54/1.77  cnf(c_0_94, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 1.54/1.77  cnf(c_0_95, negated_conjecture, (r1_tarski(k3_tarski(k2_enumset1(esk10_0,esk10_0,esk10_0,esk11_0)),esk11_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 1.54/1.77  cnf(c_0_96, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_82, c_0_81])).
% 1.54/1.77  cnf(c_0_97, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_setfam_1(k2_enumset1(X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84]), c_0_84]), c_0_44]), c_0_44])).
% 1.54/1.77  cnf(c_0_98, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_84]), c_0_44])).
% 1.54/1.77  fof(c_0_99, plain, ![X29]:k4_xboole_0(X29,k1_xboole_0)=X29, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.54/1.77  cnf(c_0_100, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 1.54/1.77  cnf(c_0_101, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 1.54/1.77  cnf(c_0_102, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 1.54/1.77  fof(c_0_103, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.54/1.77  fof(c_0_104, plain, ![X87, X88]:(~v1_relat_1(X88)|(~r2_hidden(X87,k2_relat_1(X88))|r2_hidden(esk9_2(X87,X88),k1_relat_1(X88)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).
% 1.54/1.77  cnf(c_0_105, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 1.54/1.77  cnf(c_0_106, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.54/1.77  fof(c_0_107, plain, ![X44, X45, X46]:(~r1_tarski(X44,X45)|~r1_tarski(X46,X45)|r1_tarski(k2_xboole_0(X44,X46),X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 1.54/1.77  fof(c_0_108, plain, ![X84]:(~v1_relat_1(X84)|k3_relat_1(X84)=k2_xboole_0(k1_relat_1(X84),k2_relat_1(X84))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 1.54/1.77  cnf(c_0_109, plain, (r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 1.54/1.77  cnf(c_0_110, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 1.54/1.77  cnf(c_0_111, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_43]), c_0_44])).
% 1.54/1.77  cnf(c_0_112, negated_conjecture, (k3_tarski(k2_enumset1(esk10_0,esk10_0,esk10_0,esk11_0))=esk11_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_95]), c_0_96])])).
% 1.54/1.77  cnf(c_0_113, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98]), c_0_98])).
% 1.54/1.77  cnf(c_0_114, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_99])).
% 1.54/1.77  cnf(c_0_115, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 1.54/1.77  cnf(c_0_116, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_102])).
% 1.54/1.77  cnf(c_0_117, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 1.54/1.77  fof(c_0_118, plain, ![X90, X91]:(~v1_relat_1(X90)|(~v1_relat_1(X91)|r1_tarski(k6_subset_1(k2_relat_1(X90),k2_relat_1(X91)),k2_relat_1(k6_subset_1(X90,X91))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).
% 1.54/1.77  cnf(c_0_119, plain, (r2_hidden(esk9_2(X2,X1),k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 1.54/1.77  cnf(c_0_120, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 1.54/1.77  cnf(c_0_121, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 1.54/1.77  cnf(c_0_122, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 1.54/1.77  cnf(c_0_123, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110]), c_0_110])).
% 1.54/1.77  cnf(c_0_124, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk10_0),esk11_0)=k4_xboole_0(X1,esk11_0)), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 1.54/1.77  cnf(c_0_125, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115]), c_0_115])).
% 1.54/1.77  cnf(c_0_126, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 1.54/1.77  cnf(c_0_127, plain, (r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_118])).
% 1.54/1.77  cnf(c_0_128, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_119]), c_0_120])])).
% 1.54/1.77  cnf(c_0_129, plain, (r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_43]), c_0_44])).
% 1.54/1.77  cnf(c_0_130, plain, (k3_relat_1(X1)=k3_tarski(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_43]), c_0_44])).
% 1.54/1.77  cnf(c_0_131, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_86, c_0_123])).
% 1.54/1.77  cnf(c_0_132, negated_conjecture, (k4_xboole_0(esk10_0,esk11_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_115])).
% 1.54/1.77  cnf(c_0_133, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_126])).
% 1.54/1.77  cnf(c_0_134, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.54/1.77  cnf(c_0_135, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.54/1.78  cnf(c_0_136, plain, (r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_110]), c_0_110])).
% 1.54/1.78  cnf(c_0_137, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_128, c_0_117])).
% 1.54/1.78  cnf(c_0_138, negated_conjecture, (~r1_tarski(k3_relat_1(esk10_0),k3_relat_1(esk11_0))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.54/1.78  cnf(c_0_139, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 1.54/1.78  cnf(c_0_140, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_53, c_0_130])).
% 1.54/1.78  cnf(c_0_141, negated_conjecture, (k4_xboole_0(k1_relat_1(esk10_0),k1_relat_1(esk11_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_133]), c_0_134]), c_0_135]), c_0_133]), c_0_87])])).
% 1.54/1.78  cnf(c_0_142, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(k4_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_53, c_0_81])).
% 1.54/1.78  cnf(c_0_143, plain, (k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=k2_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), inference(spm,[status(thm)],[c_0_86, c_0_136])).
% 1.54/1.78  cnf(c_0_144, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_137])).
% 1.54/1.78  cnf(c_0_145, negated_conjecture, (~r1_tarski(k2_relat_1(esk10_0),k3_relat_1(esk11_0))|~r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_139]), c_0_135])])).
% 1.54/1.78  cnf(c_0_146, negated_conjecture, (r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_134]), c_0_87])])).
% 1.54/1.78  cnf(c_0_147, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k2_relat_1(X2)),k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_142, c_0_130])).
% 1.54/1.78  cnf(c_0_148, negated_conjecture, (k4_xboole_0(k2_relat_1(esk10_0),k2_relat_1(esk11_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_132]), c_0_144]), c_0_134]), c_0_135]), c_0_144]), c_0_87])])).
% 1.54/1.78  cnf(c_0_149, negated_conjecture, (~r1_tarski(k2_relat_1(esk10_0),k3_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_145, c_0_146])])).
% 1.54/1.78  cnf(c_0_150, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_148]), c_0_134]), c_0_87])]), c_0_149]), ['proof']).
% 1.54/1.78  # SZS output end CNFRefutation
% 1.54/1.78  # Proof object total steps             : 151
% 1.54/1.78  # Proof object clause steps            : 87
% 1.54/1.78  # Proof object formula steps           : 64
% 1.54/1.78  # Proof object conjectures             : 19
% 1.54/1.78  # Proof object clause conjectures      : 16
% 1.54/1.78  # Proof object formula conjectures     : 3
% 1.54/1.78  # Proof object initial clauses used    : 36
% 1.54/1.78  # Proof object initial formulas used   : 32
% 1.54/1.78  # Proof object generating inferences   : 34
% 1.54/1.78  # Proof object simplifying inferences  : 64
% 1.54/1.78  # Training examples: 0 positive, 0 negative
% 1.54/1.78  # Parsed axioms                        : 32
% 1.54/1.78  # Removed by relevancy pruning/SinE    : 0
% 1.54/1.78  # Initial clauses                      : 49
% 1.54/1.78  # Removed in clause preprocessing      : 5
% 1.54/1.78  # Initial clauses in saturation        : 44
% 1.54/1.78  # Processed clauses                    : 5451
% 1.54/1.78  # ...of these trivial                  : 123
% 1.54/1.78  # ...subsumed                          : 4024
% 1.54/1.78  # ...remaining for further processing  : 1304
% 1.54/1.78  # Other redundant clauses eliminated   : 2
% 1.54/1.78  # Clauses deleted for lack of memory   : 0
% 1.54/1.78  # Backward-subsumed                    : 61
% 1.54/1.78  # Backward-rewritten                   : 56
% 1.54/1.78  # Generated clauses                    : 107432
% 1.54/1.78  # ...of the previous two non-trivial   : 96808
% 1.54/1.78  # Contextual simplify-reflections      : 13
% 1.54/1.78  # Paramodulations                      : 107372
% 1.54/1.78  # Factorizations                       : 6
% 1.54/1.78  # Equation resolutions                 : 53
% 1.54/1.78  # Propositional unsat checks           : 0
% 1.54/1.78  #    Propositional check models        : 0
% 1.54/1.78  #    Propositional check unsatisfiable : 0
% 1.54/1.78  #    Propositional clauses             : 0
% 1.54/1.78  #    Propositional clauses after purity: 0
% 1.54/1.78  #    Propositional unsat core size     : 0
% 1.54/1.78  #    Propositional preprocessing time  : 0.000
% 1.54/1.78  #    Propositional encoding time       : 0.000
% 1.54/1.78  #    Propositional solver time         : 0.000
% 1.54/1.78  #    Success case prop preproc time    : 0.000
% 1.54/1.78  #    Success case prop encoding time   : 0.000
% 1.54/1.78  #    Success case prop solver time     : 0.000
% 1.54/1.78  # Current number of processed clauses  : 1184
% 1.54/1.78  #    Positive orientable unit clauses  : 116
% 1.54/1.78  #    Positive unorientable unit clauses: 16
% 1.54/1.78  #    Negative unit clauses             : 29
% 1.54/1.78  #    Non-unit-clauses                  : 1023
% 1.54/1.78  # Current number of unprocessed clauses: 90906
% 1.54/1.78  # ...number of literals in the above   : 302699
% 1.54/1.78  # Current number of archived formulas  : 0
% 1.54/1.78  # Current number of archived clauses   : 123
% 1.54/1.78  # Clause-clause subsumption calls (NU) : 332067
% 1.54/1.78  # Rec. Clause-clause subsumption calls : 158568
% 1.54/1.78  # Non-unit clause-clause subsumptions  : 2550
% 1.54/1.78  # Unit Clause-clause subsumption calls : 10013
% 1.54/1.78  # Rewrite failures with RHS unbound    : 0
% 1.54/1.78  # BW rewrite match attempts            : 1865
% 1.54/1.78  # BW rewrite match successes           : 219
% 1.54/1.78  # Condensation attempts                : 0
% 1.54/1.78  # Condensation successes               : 0
% 1.54/1.78  # Termbank termtop insertions          : 1758796
% 1.61/1.78  
% 1.61/1.78  # -------------------------------------------------
% 1.61/1.78  # User time                : 1.381 s
% 1.61/1.78  # System time              : 0.059 s
% 1.61/1.78  # Total time               : 1.440 s
% 1.61/1.78  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
