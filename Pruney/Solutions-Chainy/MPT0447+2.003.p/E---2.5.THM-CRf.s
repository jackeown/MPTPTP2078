%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:22 EST 2020

% Result     : Theorem 1.02s
% Output     : CNFRefutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 389 expanded)
%              Number of clauses        :   61 ( 181 expanded)
%              Number of leaves         :   23 ( 101 expanded)
%              Depth                    :   16
%              Number of atoms          :  234 ( 740 expanded)
%              Number of equality atoms :   52 ( 258 expanded)
%              Maximal formula depth    :   15 (   3 average)
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

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r2_hidden(X1,k2_relat_1(X2))
          & ! [X3] : ~ r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

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

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_23,plain,(
    ! [X53,X54] : k1_setfam_1(k2_tarski(X53,X54)) = k3_xboole_0(X53,X54) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X47,X48] : k1_enumset1(X47,X47,X48) = k2_tarski(X47,X48) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r1_xboole_0(X13,X14)
        | r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)) )
      & ( ~ r2_hidden(X18,k3_xboole_0(X16,X17))
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X39,X40] : k4_xboole_0(X39,k4_xboole_0(X39,X40)) = k3_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_30])).

fof(c_0_34,plain,(
    ! [X32] : k4_xboole_0(X32,k1_xboole_0) = X32 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_35,plain,(
    ! [X41] : r1_xboole_0(X41,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_36,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

fof(c_0_40,plain,(
    ! [X56,X57,X58,X60,X61,X62,X63,X65] :
      ( ( ~ r2_hidden(X58,X57)
        | r2_hidden(k4_tarski(X58,esk3_3(X56,X57,X58)),X56)
        | X57 != k1_relat_1(X56) )
      & ( ~ r2_hidden(k4_tarski(X60,X61),X56)
        | r2_hidden(X60,X57)
        | X57 != k1_relat_1(X56) )
      & ( ~ r2_hidden(esk4_2(X62,X63),X63)
        | ~ r2_hidden(k4_tarski(esk4_2(X62,X63),X65),X62)
        | X63 = k1_relat_1(X62) )
      & ( r2_hidden(esk4_2(X62,X63),X63)
        | r2_hidden(k4_tarski(esk4_2(X62,X63),esk5_2(X62,X63)),X62)
        | X63 = k1_relat_1(X62) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_43,plain,(
    ! [X55] :
      ( ~ v1_xboole_0(X55)
      | v1_relat_1(X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_44,plain,(
    ! [X49,X50] : k3_tarski(k2_tarski(X49,X50)) = k2_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_45,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_46,plain,(
    ! [X70,X71] :
      ( ~ v1_relat_1(X71)
      | ~ r2_hidden(X70,k2_relat_1(X71))
      | r2_hidden(esk6_2(X70,X71),k1_relat_1(X71)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).

cnf(c_0_47,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_49,plain,(
    ! [X36,X37,X38] :
      ( ~ r1_tarski(k4_xboole_0(X36,X37),X38)
      | r1_tarski(X36,k2_xboole_0(X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_50,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_51,plain,(
    ! [X45,X46] : k2_tarski(X45,X46) = k2_tarski(X46,X45) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_52,plain,(
    ! [X73,X74] :
      ( ~ v1_relat_1(X73)
      | ~ v1_relat_1(X74)
      | r1_tarski(k6_subset_1(k2_relat_1(X73),k2_relat_1(X74)),k2_relat_1(k6_subset_1(X73,X74))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).

fof(c_0_53,plain,(
    ! [X51,X52] : k6_subset_1(X51,X52) = k4_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_54,plain,(
    ! [X21,X22] :
      ( ( k4_xboole_0(X21,X22) != k1_xboole_0
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | k4_xboole_0(X21,X22) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( r2_hidden(esk6_2(X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_58,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_59,plain,(
    ! [X42,X43,X44] :
      ( ~ r1_tarski(X42,X43)
      | ~ r1_tarski(X44,X43)
      | r1_tarski(k2_xboole_0(X42,X44),X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_60,plain,(
    ! [X67] :
      ( ~ v1_relat_1(X67)
      | k3_relat_1(X67) = k2_xboole_0(k1_relat_1(X67),k2_relat_1(X67)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_50,c_0_27])).

cnf(c_0_63,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_64,plain,(
    ! [X19,X20] :
      ( ( r1_tarski(X19,X20)
        | X19 != X20 )
      & ( r1_tarski(X20,X19)
        | X19 != X20 )
      & ( ~ r1_tarski(X19,X20)
        | ~ r1_tarski(X20,X19)
        | X19 = X20 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_65,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_69,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_70,plain,(
    ! [X68,X69] :
      ( ~ v1_relat_1(X68)
      | ~ v1_relat_1(X69)
      | r1_tarski(k6_subset_1(k1_relat_1(X68),k1_relat_1(X69)),k1_relat_1(k6_subset_1(X68,X69))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).

fof(c_0_71,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

cnf(c_0_72,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_75,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_27]),c_0_27])).

cnf(c_0_76,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_66])).

cnf(c_0_78,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_67])).

cnf(c_0_79,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_80,plain,(
    ! [X29] : r1_tarski(k1_xboole_0,X29) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_81,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_82,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_relat_1(esk8_0)
    & r1_tarski(esk7_0,esk8_0)
    & ~ r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_71])])])).

cnf(c_0_83,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_62])).

cnf(c_0_84,plain,
    ( k3_relat_1(X1) = k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_73,c_0_62])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_86,plain,
    ( k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) = k2_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_87,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_89,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_66]),c_0_66])).

cnf(c_0_90,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_69])).

cnf(c_0_91,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_92,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k2_relat_1(X2)),k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_84])).

cnf(c_0_95,plain,
    ( k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_67]),c_0_87]),c_0_87]),c_0_88])])).

cnf(c_0_96,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_89])).

cnf(c_0_97,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk7_0),k3_relat_1(esk8_0))
    | ~ r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])])).

cnf(c_0_99,plain,
    ( r1_tarski(k2_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_88])])).

cnf(c_0_100,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_84])).

cnf(c_0_103,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_67]),c_0_97]),c_0_97]),c_0_88])])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100]),c_0_93]),c_0_101])])).

cnf(c_0_105,plain,
    ( r1_tarski(k1_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_88])])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_100]),c_0_93]),c_0_101])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:38:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.02/1.18  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 1.02/1.18  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.02/1.18  #
% 1.02/1.18  # Preprocessing time       : 0.029 s
% 1.02/1.18  
% 1.02/1.18  # Proof found!
% 1.02/1.18  # SZS status Theorem
% 1.02/1.18  # SZS output start CNFRefutation
% 1.02/1.18  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.02/1.18  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.02/1.18  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.02/1.18  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.02/1.18  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.02/1.18  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.02/1.18  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.02/1.18  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.02/1.18  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.02/1.18  fof(t19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~((r2_hidden(X1,k2_relat_1(X2))&![X3]:~(r2_hidden(X3,k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 1.02/1.18  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.02/1.18  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.02/1.18  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.02/1.18  fof(t28_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 1.02/1.18  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.02/1.18  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.02/1.18  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.02/1.18  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.02/1.18  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.02/1.18  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.02/1.18  fof(t15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 1.02/1.18  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 1.02/1.18  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.02/1.18  fof(c_0_23, plain, ![X53, X54]:k1_setfam_1(k2_tarski(X53,X54))=k3_xboole_0(X53,X54), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.02/1.18  fof(c_0_24, plain, ![X47, X48]:k1_enumset1(X47,X47,X48)=k2_tarski(X47,X48), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.02/1.18  fof(c_0_25, plain, ![X13, X14, X16, X17, X18]:((r1_xboole_0(X13,X14)|r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)))&(~r2_hidden(X18,k3_xboole_0(X16,X17))|~r1_xboole_0(X16,X17))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 1.02/1.18  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.02/1.18  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.02/1.18  fof(c_0_28, plain, ![X39, X40]:k4_xboole_0(X39,k4_xboole_0(X39,X40))=k3_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.02/1.18  cnf(c_0_29, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.02/1.18  cnf(c_0_30, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 1.02/1.18  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.02/1.18  cnf(c_0_32, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 1.02/1.18  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[c_0_31, c_0_30])).
% 1.02/1.18  fof(c_0_34, plain, ![X32]:k4_xboole_0(X32,k1_xboole_0)=X32, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.02/1.18  fof(c_0_35, plain, ![X41]:r1_xboole_0(X41,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 1.02/1.18  cnf(c_0_36, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 1.02/1.18  cnf(c_0_37, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.02/1.18  cnf(c_0_38, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.02/1.18  cnf(c_0_39, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 1.02/1.18  fof(c_0_40, plain, ![X56, X57, X58, X60, X61, X62, X63, X65]:(((~r2_hidden(X58,X57)|r2_hidden(k4_tarski(X58,esk3_3(X56,X57,X58)),X56)|X57!=k1_relat_1(X56))&(~r2_hidden(k4_tarski(X60,X61),X56)|r2_hidden(X60,X57)|X57!=k1_relat_1(X56)))&((~r2_hidden(esk4_2(X62,X63),X63)|~r2_hidden(k4_tarski(esk4_2(X62,X63),X65),X62)|X63=k1_relat_1(X62))&(r2_hidden(esk4_2(X62,X63),X63)|r2_hidden(k4_tarski(esk4_2(X62,X63),esk5_2(X62,X63)),X62)|X63=k1_relat_1(X62)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.02/1.18  cnf(c_0_41, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_37])).
% 1.02/1.18  cnf(c_0_42, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.02/1.18  fof(c_0_43, plain, ![X55]:(~v1_xboole_0(X55)|v1_relat_1(X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 1.02/1.18  fof(c_0_44, plain, ![X49, X50]:k3_tarski(k2_tarski(X49,X50))=k2_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.02/1.18  cnf(c_0_45, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.02/1.18  fof(c_0_46, plain, ![X70, X71]:(~v1_relat_1(X71)|(~r2_hidden(X70,k2_relat_1(X71))|r2_hidden(esk6_2(X70,X71),k1_relat_1(X71)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).
% 1.02/1.18  cnf(c_0_47, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.02/1.18  cnf(c_0_48, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.02/1.18  fof(c_0_49, plain, ![X36, X37, X38]:(~r1_tarski(k4_xboole_0(X36,X37),X38)|r1_tarski(X36,k2_xboole_0(X37,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 1.02/1.18  cnf(c_0_50, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.02/1.18  fof(c_0_51, plain, ![X45, X46]:k2_tarski(X45,X46)=k2_tarski(X46,X45), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.02/1.18  fof(c_0_52, plain, ![X73, X74]:(~v1_relat_1(X73)|(~v1_relat_1(X74)|r1_tarski(k6_subset_1(k2_relat_1(X73),k2_relat_1(X74)),k2_relat_1(k6_subset_1(X73,X74))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).
% 1.02/1.18  fof(c_0_53, plain, ![X51, X52]:k6_subset_1(X51,X52)=k4_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 1.02/1.18  fof(c_0_54, plain, ![X21, X22]:((k4_xboole_0(X21,X22)!=k1_xboole_0|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|k4_xboole_0(X21,X22)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.02/1.18  cnf(c_0_55, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_45])).
% 1.02/1.18  cnf(c_0_56, plain, (r2_hidden(esk6_2(X2,X1),k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.02/1.18  cnf(c_0_57, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.02/1.18  fof(c_0_58, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.02/1.18  fof(c_0_59, plain, ![X42, X43, X44]:(~r1_tarski(X42,X43)|~r1_tarski(X44,X43)|r1_tarski(k2_xboole_0(X42,X44),X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 1.02/1.18  fof(c_0_60, plain, ![X67]:(~v1_relat_1(X67)|k3_relat_1(X67)=k2_xboole_0(k1_relat_1(X67),k2_relat_1(X67))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 1.02/1.18  cnf(c_0_61, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.02/1.18  cnf(c_0_62, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_50, c_0_27])).
% 1.02/1.18  cnf(c_0_63, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.02/1.18  fof(c_0_64, plain, ![X19, X20]:(((r1_tarski(X19,X20)|X19!=X20)&(r1_tarski(X20,X19)|X19!=X20))&(~r1_tarski(X19,X20)|~r1_tarski(X20,X19)|X19=X20)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.02/1.18  cnf(c_0_65, plain, (r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.02/1.18  cnf(c_0_66, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.02/1.18  cnf(c_0_67, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.02/1.18  cnf(c_0_68, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 1.02/1.18  cnf(c_0_69, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.02/1.18  fof(c_0_70, plain, ![X68, X69]:(~v1_relat_1(X68)|(~v1_relat_1(X69)|r1_tarski(k6_subset_1(k1_relat_1(X68),k1_relat_1(X69)),k1_relat_1(k6_subset_1(X68,X69))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).
% 1.02/1.18  fof(c_0_71, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 1.02/1.18  cnf(c_0_72, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.02/1.18  cnf(c_0_73, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.02/1.18  cnf(c_0_74, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 1.02/1.18  cnf(c_0_75, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_27]), c_0_27])).
% 1.02/1.18  cnf(c_0_76, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 1.02/1.18  cnf(c_0_77, plain, (r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66]), c_0_66])).
% 1.02/1.18  cnf(c_0_78, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_67])).
% 1.02/1.18  cnf(c_0_79, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 1.02/1.18  fof(c_0_80, plain, ![X29]:r1_tarski(k1_xboole_0,X29), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.02/1.18  cnf(c_0_81, plain, (r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.02/1.18  fof(c_0_82, negated_conjecture, (v1_relat_1(esk7_0)&(v1_relat_1(esk8_0)&(r1_tarski(esk7_0,esk8_0)&~r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_71])])])).
% 1.02/1.18  cnf(c_0_83, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_62])).
% 1.02/1.18  cnf(c_0_84, plain, (k3_relat_1(X1)=k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_73, c_0_62])).
% 1.02/1.18  cnf(c_0_85, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_tarski(k4_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 1.02/1.18  cnf(c_0_86, plain, (k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=k2_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 1.02/1.18  cnf(c_0_87, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 1.02/1.18  cnf(c_0_88, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.02/1.18  cnf(c_0_89, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_66]), c_0_66])).
% 1.02/1.18  cnf(c_0_90, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_55, c_0_69])).
% 1.02/1.18  cnf(c_0_91, negated_conjecture, (~r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.02/1.18  cnf(c_0_92, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 1.02/1.18  cnf(c_0_93, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.02/1.18  cnf(c_0_94, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k2_relat_1(X2)),k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_85, c_0_84])).
% 1.02/1.18  cnf(c_0_95, plain, (k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_67]), c_0_87]), c_0_87]), c_0_88])])).
% 1.02/1.18  cnf(c_0_96, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_76, c_0_89])).
% 1.02/1.18  cnf(c_0_97, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_90])).
% 1.02/1.18  cnf(c_0_98, negated_conjecture, (~r1_tarski(k2_relat_1(esk7_0),k3_relat_1(esk8_0))|~r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])])).
% 1.02/1.18  cnf(c_0_99, plain, (r1_tarski(k2_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_88])])).
% 1.02/1.18  cnf(c_0_100, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.02/1.18  cnf(c_0_101, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.02/1.18  cnf(c_0_102, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_74, c_0_84])).
% 1.02/1.18  cnf(c_0_103, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_67]), c_0_97]), c_0_97]), c_0_88])])).
% 1.02/1.18  cnf(c_0_104, negated_conjecture, (~r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100]), c_0_93]), c_0_101])])).
% 1.02/1.18  cnf(c_0_105, plain, (r1_tarski(k1_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_88])])).
% 1.02/1.18  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_100]), c_0_93]), c_0_101])]), ['proof']).
% 1.02/1.18  # SZS output end CNFRefutation
% 1.02/1.18  # Proof object total steps             : 107
% 1.02/1.18  # Proof object clause steps            : 61
% 1.02/1.18  # Proof object formula steps           : 46
% 1.02/1.18  # Proof object conjectures             : 10
% 1.02/1.18  # Proof object clause conjectures      : 7
% 1.02/1.18  # Proof object formula conjectures     : 3
% 1.02/1.18  # Proof object initial clauses used    : 26
% 1.02/1.18  # Proof object initial formulas used   : 23
% 1.02/1.18  # Proof object generating inferences   : 24
% 1.02/1.18  # Proof object simplifying inferences  : 40
% 1.02/1.18  # Training examples: 0 positive, 0 negative
% 1.02/1.18  # Parsed axioms                        : 28
% 1.02/1.18  # Removed by relevancy pruning/SinE    : 0
% 1.02/1.18  # Initial clauses                      : 40
% 1.02/1.18  # Removed in clause preprocessing      : 4
% 1.02/1.18  # Initial clauses in saturation        : 36
% 1.02/1.18  # Processed clauses                    : 5043
% 1.02/1.18  # ...of these trivial                  : 67
% 1.02/1.18  # ...subsumed                          : 3861
% 1.02/1.18  # ...remaining for further processing  : 1115
% 1.02/1.18  # Other redundant clauses eliminated   : 2
% 1.02/1.18  # Clauses deleted for lack of memory   : 0
% 1.02/1.18  # Backward-subsumed                    : 43
% 1.02/1.18  # Backward-rewritten                   : 18
% 1.02/1.18  # Generated clauses                    : 69214
% 1.02/1.18  # ...of the previous two non-trivial   : 61356
% 1.02/1.18  # Contextual simplify-reflections      : 12
% 1.02/1.18  # Paramodulations                      : 69175
% 1.02/1.18  # Factorizations                       : 4
% 1.02/1.18  # Equation resolutions                 : 34
% 1.02/1.18  # Propositional unsat checks           : 0
% 1.02/1.18  #    Propositional check models        : 0
% 1.02/1.18  #    Propositional check unsatisfiable : 0
% 1.02/1.18  #    Propositional clauses             : 0
% 1.02/1.18  #    Propositional clauses after purity: 0
% 1.02/1.18  #    Propositional unsat core size     : 0
% 1.02/1.18  #    Propositional preprocessing time  : 0.000
% 1.02/1.18  #    Propositional encoding time       : 0.000
% 1.02/1.18  #    Propositional solver time         : 0.000
% 1.02/1.18  #    Success case prop preproc time    : 0.000
% 1.02/1.18  #    Success case prop encoding time   : 0.000
% 1.02/1.18  #    Success case prop solver time     : 0.000
% 1.02/1.18  # Current number of processed clauses  : 1051
% 1.02/1.18  #    Positive orientable unit clauses  : 93
% 1.02/1.18  #    Positive unorientable unit clauses: 2
% 1.02/1.18  #    Negative unit clauses             : 24
% 1.02/1.18  #    Non-unit-clauses                  : 932
% 1.02/1.18  # Current number of unprocessed clauses: 56223
% 1.02/1.18  # ...number of literals in the above   : 176359
% 1.02/1.18  # Current number of archived formulas  : 0
% 1.02/1.18  # Current number of archived clauses   : 66
% 1.02/1.18  # Clause-clause subsumption calls (NU) : 194415
% 1.02/1.18  # Rec. Clause-clause subsumption calls : 121135
% 1.02/1.18  # Non-unit clause-clause subsumptions  : 2379
% 1.02/1.18  # Unit Clause-clause subsumption calls : 5740
% 1.02/1.18  # Rewrite failures with RHS unbound    : 0
% 1.02/1.18  # BW rewrite match attempts            : 2209
% 1.02/1.18  # BW rewrite match successes           : 18
% 1.02/1.18  # Condensation attempts                : 0
% 1.02/1.18  # Condensation successes               : 0
% 1.02/1.18  # Termbank termtop insertions          : 1127272
% 1.02/1.19  
% 1.02/1.19  # -------------------------------------------------
% 1.02/1.19  # User time                : 0.819 s
% 1.02/1.19  # System time              : 0.031 s
% 1.02/1.19  # Total time               : 0.851 s
% 1.02/1.19  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
