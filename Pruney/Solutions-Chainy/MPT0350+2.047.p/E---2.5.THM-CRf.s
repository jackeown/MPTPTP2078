%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:20 EST 2020

% Result     : Theorem 33.23s
% Output     : CNFRefutation 33.23s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 766 expanded)
%              Number of clauses        :   89 ( 344 expanded)
%              Number of leaves         :   25 ( 208 expanded)
%              Depth                    :   13
%              Number of atoms          :  243 (1250 expanded)
%              Number of equality atoms :  116 ( 730 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

fof(c_0_26,plain,(
    ! [X29,X30] : r1_tarski(k4_xboole_0(X29,X30),X29) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_27,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_28,plain,(
    ! [X24,X25,X26] : k5_xboole_0(k3_xboole_0(X24,X25),k3_xboole_0(X26,X25)) = k3_xboole_0(k5_xboole_0(X24,X26),X25) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_29,plain,(
    ! [X21] : k3_xboole_0(X21,X21) = X21 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_30,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_31,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_32,plain,(
    ! [X31] : k5_xboole_0(X31,k1_xboole_0) = X31 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_33,plain,(
    ! [X64,X65,X66,X67,X68,X69] :
      ( ( ~ r2_hidden(X66,X65)
        | r1_tarski(X66,X64)
        | X65 != k1_zfmisc_1(X64) )
      & ( ~ r1_tarski(X67,X64)
        | r2_hidden(X67,X65)
        | X65 != k1_zfmisc_1(X64) )
      & ( ~ r2_hidden(esk2_2(X68,X69),X69)
        | ~ r1_tarski(esk2_2(X68,X69),X68)
        | X69 = k1_zfmisc_1(X68) )
      & ( r2_hidden(esk2_2(X68,X69),X69)
        | r1_tarski(esk2_2(X68,X69),X68)
        | X69 = k1_zfmisc_1(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_34,plain,(
    ! [X73,X74] :
      ( ( ~ m1_subset_1(X74,X73)
        | r2_hidden(X74,X73)
        | v1_xboole_0(X73) )
      & ( ~ r2_hidden(X74,X73)
        | m1_subset_1(X74,X73)
        | v1_xboole_0(X73) )
      & ( ~ m1_subset_1(X74,X73)
        | v1_xboole_0(X74)
        | ~ v1_xboole_0(X73) )
      & ( ~ v1_xboole_0(X74)
        | m1_subset_1(X74,X73)
        | ~ v1_xboole_0(X73) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    & k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0)) != k2_subset_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_36,plain,(
    ! [X78] : ~ v1_xboole_0(k1_zfmisc_1(X78)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_48,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( r2_hidden(X15,X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X17,X18,X19),X19)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X17)
        | r2_hidden(esk1_3(X17,X18,X19),X18)
        | X19 = k4_xboole_0(X17,X18) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X17)
        | r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk1_3(X17,X18,X19),X18)
        | r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k4_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_49,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,X1)) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

fof(c_0_52,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k3_xboole_0(X27,X28) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_57,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_41])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_40])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_63,plain,(
    ! [X71,X72] : k3_tarski(k2_tarski(X71,X72)) = k2_xboole_0(X71,X72) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_64,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_65,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_38])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_59,c_0_38])).

cnf(c_0_69,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_60,c_0_38])).

fof(c_0_70,plain,(
    ! [X32,X33,X34] : k5_xboole_0(k5_xboole_0(X32,X33),X34) = k5_xboole_0(X32,k5_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_41])).

fof(c_0_72,plain,(
    ! [X35,X36] : k2_xboole_0(X35,X36) = k5_xboole_0(k5_xboole_0(X35,X36),k3_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_73,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_75,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_76,plain,(
    ! [X42,X43,X44,X45] : k3_enumset1(X42,X42,X43,X44,X45) = k2_enumset1(X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_77,plain,(
    ! [X46,X47,X48,X49,X50] : k4_enumset1(X46,X46,X47,X48,X49,X50) = k3_enumset1(X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_78,plain,(
    ! [X51,X52,X53,X54,X55,X56] : k5_enumset1(X51,X51,X52,X53,X54,X55,X56) = k4_enumset1(X51,X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_79,plain,(
    ! [X57,X58,X59,X60,X61,X62,X63] : k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63) = k5_enumset1(X57,X58,X59,X60,X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_82,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_41])).

cnf(c_0_83,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)) = k3_xboole_0(k5_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_41])).

cnf(c_0_84,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_51])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_69])).

cnf(c_0_87,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_88,plain,(
    ! [X76,X77] :
      ( ~ m1_subset_1(X77,k1_zfmisc_1(X76))
      | k3_subset_1(X76,X77) = k4_xboole_0(X76,X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_89,plain,(
    ! [X79,X80,X81] :
      ( ~ m1_subset_1(X80,k1_zfmisc_1(X79))
      | ~ m1_subset_1(X81,k1_zfmisc_1(X79))
      | k4_subset_1(X79,X80,X81) = k2_xboole_0(X80,X81) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_71])).

cnf(c_0_91,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_92,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_93,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_94,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_95,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_96,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_97,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_98,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_zfmisc_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_99,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X1),X2) = k3_xboole_0(k5_xboole_0(X2,X2),X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_100,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_84]),c_0_41])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

fof(c_0_102,plain,(
    ! [X75] : k2_subset_1(X75) = X75 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_103,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_104,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_105,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_90])).

cnf(c_0_107,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92]),c_0_93]),c_0_94]),c_0_95]),c_0_96]),c_0_97])).

cnf(c_0_108,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk4_0)) = k5_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_90]),c_0_41])).

cnf(c_0_109,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X1)),X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_87])).

cnf(c_0_110,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_100]),c_0_51])).

cnf(c_0_111,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X1,k1_xboole_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_58]),c_0_40]),c_0_51]),c_0_51])).

cnf(c_0_112,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_50]),c_0_43]),c_0_51]),c_0_43])).

cnf(c_0_113,plain,
    ( r1_tarski(k3_xboole_0(X1,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_41])).

cnf(c_0_114,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0)) != k2_subset_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_115,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_116,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_103,c_0_38])).

cnf(c_0_117,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_92]),c_0_93]),c_0_94]),c_0_95]),c_0_96]),c_0_97])).

cnf(c_0_118,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_47])).

cnf(c_0_119,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_107,c_0_87])).

cnf(c_0_120,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(X1,k5_xboole_0(esk3_0,esk4_0)))) = k3_xboole_0(k5_xboole_0(X1,esk3_0),k5_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_108]),c_0_42]),c_0_87])).

cnf(c_0_121,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k5_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X1)),k3_xboole_0(k1_xboole_0,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_110])).

cnf(c_0_122,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r2_hidden(esk1_3(k1_xboole_0,X1,k1_xboole_0),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_111]),c_0_112])).

cnf(c_0_123,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_113]),c_0_41])).

cnf(c_0_124,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_125,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_126,negated_conjecture,
    ( k3_subset_1(esk3_0,esk4_0) = k5_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_46]),c_0_71])).

cnf(c_0_127,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,esk3_0),k5_xboole_0(esk3_0,esk4_0))) = k4_subset_1(esk3_0,X1,k5_xboole_0(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119]),c_0_87]),c_0_120])).

cnf(c_0_128,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_42])).

cnf(c_0_129,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k3_xboole_0(k1_xboole_0,X2),k5_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_121,c_0_41])).

cnf(c_0_130,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_122,c_0_81])).

cnf(c_0_131,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_123]),c_0_39]),c_0_41])).

cnf(c_0_132,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_124,c_0_38])).

cnf(c_0_133,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_134,negated_conjecture,
    ( k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0)) = k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_46]),c_0_42]),c_0_40]),c_0_128])).

cnf(c_0_135,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_130]),c_0_131]),c_0_41]),c_0_130])).

cnf(c_0_136,plain,
    ( X1 = k5_xboole_0(X2,X2)
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_69]),c_0_40])).

cnf(c_0_137,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk4_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_138,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_139,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_138]),c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 33.23/33.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 33.23/33.45  # and selection function GSelectMinInfpos.
% 33.23/33.45  #
% 33.23/33.45  # Preprocessing time       : 0.027 s
% 33.23/33.45  # Presaturation interreduction done
% 33.23/33.45  
% 33.23/33.45  # Proof found!
% 33.23/33.45  # SZS status Theorem
% 33.23/33.45  # SZS output start CNFRefutation
% 33.23/33.45  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 33.23/33.45  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 33.23/33.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 33.23/33.45  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 33.23/33.45  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 33.23/33.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 33.23/33.45  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 33.23/33.45  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 33.23/33.45  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 33.23/33.45  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 33.23/33.45  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 33.23/33.45  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 33.23/33.45  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 33.23/33.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 33.23/33.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 33.23/33.45  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 33.23/33.45  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 33.23/33.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 33.23/33.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 33.23/33.45  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 33.23/33.45  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 33.23/33.45  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 33.23/33.45  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 33.23/33.45  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 33.23/33.45  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 33.23/33.45  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 33.23/33.45  fof(c_0_26, plain, ![X29, X30]:r1_tarski(k4_xboole_0(X29,X30),X29), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 33.23/33.45  fof(c_0_27, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 33.23/33.45  fof(c_0_28, plain, ![X24, X25, X26]:k5_xboole_0(k3_xboole_0(X24,X25),k3_xboole_0(X26,X25))=k3_xboole_0(k5_xboole_0(X24,X26),X25), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 33.23/33.45  fof(c_0_29, plain, ![X21]:k3_xboole_0(X21,X21)=X21, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 33.23/33.45  fof(c_0_30, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 33.23/33.45  fof(c_0_31, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 33.23/33.45  fof(c_0_32, plain, ![X31]:k5_xboole_0(X31,k1_xboole_0)=X31, inference(variable_rename,[status(thm)],[t5_boole])).
% 33.23/33.45  fof(c_0_33, plain, ![X64, X65, X66, X67, X68, X69]:(((~r2_hidden(X66,X65)|r1_tarski(X66,X64)|X65!=k1_zfmisc_1(X64))&(~r1_tarski(X67,X64)|r2_hidden(X67,X65)|X65!=k1_zfmisc_1(X64)))&((~r2_hidden(esk2_2(X68,X69),X69)|~r1_tarski(esk2_2(X68,X69),X68)|X69=k1_zfmisc_1(X68))&(r2_hidden(esk2_2(X68,X69),X69)|r1_tarski(esk2_2(X68,X69),X68)|X69=k1_zfmisc_1(X68)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 33.23/33.45  fof(c_0_34, plain, ![X73, X74]:(((~m1_subset_1(X74,X73)|r2_hidden(X74,X73)|v1_xboole_0(X73))&(~r2_hidden(X74,X73)|m1_subset_1(X74,X73)|v1_xboole_0(X73)))&((~m1_subset_1(X74,X73)|v1_xboole_0(X74)|~v1_xboole_0(X73))&(~v1_xboole_0(X74)|m1_subset_1(X74,X73)|~v1_xboole_0(X73)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 33.23/33.45  fof(c_0_35, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0))!=k2_subset_1(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 33.23/33.45  fof(c_0_36, plain, ![X78]:~v1_xboole_0(k1_zfmisc_1(X78)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 33.23/33.45  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 33.23/33.45  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 33.23/33.45  cnf(c_0_39, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 33.23/33.45  cnf(c_0_40, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 33.23/33.45  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 33.23/33.45  cnf(c_0_42, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 33.23/33.45  cnf(c_0_43, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 33.23/33.45  cnf(c_0_44, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 33.23/33.45  cnf(c_0_45, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 33.23/33.45  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 33.23/33.45  cnf(c_0_47, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 33.23/33.45  fof(c_0_48, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:((((r2_hidden(X15,X12)|~r2_hidden(X15,X14)|X14!=k4_xboole_0(X12,X13))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|X14!=k4_xboole_0(X12,X13)))&(~r2_hidden(X16,X12)|r2_hidden(X16,X13)|r2_hidden(X16,X14)|X14!=k4_xboole_0(X12,X13)))&((~r2_hidden(esk1_3(X17,X18,X19),X19)|(~r2_hidden(esk1_3(X17,X18,X19),X17)|r2_hidden(esk1_3(X17,X18,X19),X18))|X19=k4_xboole_0(X17,X18))&((r2_hidden(esk1_3(X17,X18,X19),X17)|r2_hidden(esk1_3(X17,X18,X19),X19)|X19=k4_xboole_0(X17,X18))&(~r2_hidden(esk1_3(X17,X18,X19),X18)|r2_hidden(esk1_3(X17,X18,X19),X19)|X19=k4_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 33.23/33.45  cnf(c_0_49, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 33.23/33.45  cnf(c_0_50, plain, (k3_xboole_0(X1,k5_xboole_0(X2,X1))=k5_xboole_0(X1,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])).
% 33.23/33.45  cnf(c_0_51, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 33.23/33.45  fof(c_0_52, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k3_xboole_0(X27,X28)=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 33.23/33.45  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_44])).
% 33.23/33.45  cnf(c_0_54, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 33.23/33.45  cnf(c_0_55, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 33.23/33.45  cnf(c_0_56, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 33.23/33.45  cnf(c_0_57, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_49, c_0_41])).
% 33.23/33.45  cnf(c_0_58, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_40])).
% 33.23/33.45  cnf(c_0_59, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 33.23/33.45  cnf(c_0_60, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 33.23/33.45  cnf(c_0_61, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 33.23/33.45  cnf(c_0_62, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 33.23/33.45  fof(c_0_63, plain, ![X71, X72]:k3_tarski(k2_tarski(X71,X72))=k2_xboole_0(X71,X72), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 33.23/33.45  fof(c_0_64, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 33.23/33.45  cnf(c_0_65, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_55, c_0_38])).
% 33.23/33.45  cnf(c_0_66, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_56])).
% 33.23/33.45  cnf(c_0_67, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 33.23/33.45  cnf(c_0_68, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_59, c_0_38])).
% 33.23/33.45  cnf(c_0_69, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_60, c_0_38])).
% 33.23/33.45  fof(c_0_70, plain, ![X32, X33, X34]:k5_xboole_0(k5_xboole_0(X32,X33),X34)=k5_xboole_0(X32,k5_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 33.23/33.45  cnf(c_0_71, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_41])).
% 33.23/33.45  fof(c_0_72, plain, ![X35, X36]:k2_xboole_0(X35,X36)=k5_xboole_0(k5_xboole_0(X35,X36),k3_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 33.23/33.45  cnf(c_0_73, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 33.23/33.45  cnf(c_0_74, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 33.23/33.45  fof(c_0_75, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 33.23/33.45  fof(c_0_76, plain, ![X42, X43, X44, X45]:k3_enumset1(X42,X42,X43,X44,X45)=k2_enumset1(X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 33.23/33.45  fof(c_0_77, plain, ![X46, X47, X48, X49, X50]:k4_enumset1(X46,X46,X47,X48,X49,X50)=k3_enumset1(X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 33.23/33.45  fof(c_0_78, plain, ![X51, X52, X53, X54, X55, X56]:k5_enumset1(X51,X51,X52,X53,X54,X55,X56)=k4_enumset1(X51,X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 33.23/33.45  fof(c_0_79, plain, ![X57, X58, X59, X60, X61, X62, X63]:k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63)=k5_enumset1(X57,X58,X59,X60,X61,X62,X63), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 33.23/33.45  cnf(c_0_80, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_65])).
% 33.23/33.45  cnf(c_0_81, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 33.23/33.45  cnf(c_0_82, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_39, c_0_41])).
% 33.23/33.45  cnf(c_0_83, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))=k3_xboole_0(k5_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_39, c_0_41])).
% 33.23/33.45  cnf(c_0_84, plain, (r1_tarski(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_51])).
% 33.23/33.45  cnf(c_0_85, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_68])).
% 33.23/33.45  cnf(c_0_86, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_69])).
% 33.23/33.45  cnf(c_0_87, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 33.23/33.45  fof(c_0_88, plain, ![X76, X77]:(~m1_subset_1(X77,k1_zfmisc_1(X76))|k3_subset_1(X76,X77)=k4_xboole_0(X76,X77)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 33.23/33.45  fof(c_0_89, plain, ![X79, X80, X81]:(~m1_subset_1(X80,k1_zfmisc_1(X79))|~m1_subset_1(X81,k1_zfmisc_1(X79))|k4_subset_1(X79,X80,X81)=k2_xboole_0(X80,X81)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 33.23/33.45  cnf(c_0_90, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_71])).
% 33.23/33.45  cnf(c_0_91, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 33.23/33.45  cnf(c_0_92, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 33.23/33.45  cnf(c_0_93, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 33.23/33.45  cnf(c_0_94, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 33.23/33.45  cnf(c_0_95, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 33.23/33.45  cnf(c_0_96, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 33.23/33.45  cnf(c_0_97, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 33.23/33.45  cnf(c_0_98, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_zfmisc_1(X1))))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 33.23/33.45  cnf(c_0_99, plain, (k3_xboole_0(k5_xboole_0(X1,X1),X2)=k3_xboole_0(k5_xboole_0(X2,X2),X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 33.23/33.45  cnf(c_0_100, plain, (k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k3_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_84]), c_0_41])).
% 33.23/33.45  cnf(c_0_101, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 33.23/33.45  fof(c_0_102, plain, ![X75]:k2_subset_1(X75)=X75, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 33.23/33.45  cnf(c_0_103, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 33.23/33.45  cnf(c_0_104, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 33.23/33.45  cnf(c_0_105, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 33.23/33.45  cnf(c_0_106, negated_conjecture, (r2_hidden(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_66, c_0_90])).
% 33.23/33.45  cnf(c_0_107, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92]), c_0_93]), c_0_94]), c_0_95]), c_0_96]), c_0_97])).
% 33.23/33.45  cnf(c_0_108, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk4_0))=k5_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_90]), c_0_41])).
% 33.23/33.45  cnf(c_0_109, plain, (~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X1)),X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_87])).
% 33.23/33.45  cnf(c_0_110, plain, (k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)))=k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_100]), c_0_51])).
% 33.23/33.45  cnf(c_0_111, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X1,k1_xboole_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_58]), c_0_40]), c_0_51]), c_0_51])).
% 33.23/33.45  cnf(c_0_112, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_50]), c_0_43]), c_0_51]), c_0_43])).
% 33.23/33.45  cnf(c_0_113, plain, (r1_tarski(k3_xboole_0(X1,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_84, c_0_41])).
% 33.23/33.45  cnf(c_0_114, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0))!=k2_subset_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 33.23/33.45  cnf(c_0_115, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_102])).
% 33.23/33.45  cnf(c_0_116, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_103, c_0_38])).
% 33.23/33.45  cnf(c_0_117, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_92]), c_0_93]), c_0_94]), c_0_95]), c_0_96]), c_0_97])).
% 33.23/33.45  cnf(c_0_118, negated_conjecture, (m1_subset_1(k5_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_47])).
% 33.23/33.45  cnf(c_0_119, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_107, c_0_87])).
% 33.23/33.45  cnf(c_0_120, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(X1,k5_xboole_0(esk3_0,esk4_0))))=k3_xboole_0(k5_xboole_0(X1,esk3_0),k5_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_108]), c_0_42]), c_0_87])).
% 33.23/33.45  cnf(c_0_121, plain, (~r2_hidden(X1,k3_xboole_0(k5_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X1)),k3_xboole_0(k1_xboole_0,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_110])).
% 33.23/33.45  cnf(c_0_122, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r2_hidden(esk1_3(k1_xboole_0,X1,k1_xboole_0),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_111]), c_0_112])).
% 33.23/33.45  cnf(c_0_123, plain, (k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0))=k3_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_113]), c_0_41])).
% 33.23/33.45  cnf(c_0_124, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 33.23/33.45  cnf(c_0_125, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk4_0))!=esk3_0), inference(rw,[status(thm)],[c_0_114, c_0_115])).
% 33.23/33.45  cnf(c_0_126, negated_conjecture, (k3_subset_1(esk3_0,esk4_0)=k5_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_46]), c_0_71])).
% 33.23/33.45  cnf(c_0_127, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,esk3_0),k5_xboole_0(esk3_0,esk4_0)))=k4_subset_1(esk3_0,X1,k5_xboole_0(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_119]), c_0_87]), c_0_120])).
% 33.23/33.45  cnf(c_0_128, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_87, c_0_42])).
% 33.23/33.45  cnf(c_0_129, plain, (~r2_hidden(X1,k3_xboole_0(k3_xboole_0(k1_xboole_0,X2),k5_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X1))))), inference(spm,[status(thm)],[c_0_121, c_0_41])).
% 33.23/33.45  cnf(c_0_130, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_122, c_0_81])).
% 33.23/33.45  cnf(c_0_131, plain, (k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1))=k3_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_123]), c_0_39]), c_0_41])).
% 33.23/33.45  cnf(c_0_132, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_124, c_0_38])).
% 33.23/33.45  cnf(c_0_133, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0))!=esk3_0), inference(rw,[status(thm)],[c_0_125, c_0_126])).
% 33.23/33.45  cnf(c_0_134, negated_conjecture, (k4_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk4_0))=k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_46]), c_0_42]), c_0_40]), c_0_128])).
% 33.23/33.45  cnf(c_0_135, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_130]), c_0_131]), c_0_41]), c_0_130])).
% 33.23/33.45  cnf(c_0_136, plain, (X1=k5_xboole_0(X2,X2)|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_69]), c_0_40])).
% 33.23/33.45  cnf(c_0_137, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk4_0))!=esk3_0), inference(rw,[status(thm)],[c_0_133, c_0_134])).
% 33.23/33.45  cnf(c_0_138, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 33.23/33.45  cnf(c_0_139, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137, c_0_138]), c_0_43])]), ['proof']).
% 33.23/33.45  # SZS output end CNFRefutation
% 33.23/33.45  # Proof object total steps             : 140
% 33.23/33.45  # Proof object clause steps            : 89
% 33.23/33.45  # Proof object formula steps           : 51
% 33.23/33.45  # Proof object conjectures             : 20
% 33.23/33.45  # Proof object clause conjectures      : 17
% 33.23/33.45  # Proof object formula conjectures     : 3
% 33.23/33.45  # Proof object initial clauses used    : 31
% 33.23/33.45  # Proof object initial formulas used   : 25
% 33.23/33.45  # Proof object generating inferences   : 39
% 33.23/33.45  # Proof object simplifying inferences  : 66
% 33.23/33.45  # Training examples: 0 positive, 0 negative
% 33.23/33.45  # Parsed axioms                        : 25
% 33.23/33.45  # Removed by relevancy pruning/SinE    : 0
% 33.23/33.45  # Initial clauses                      : 37
% 33.23/33.45  # Removed in clause preprocessing      : 9
% 33.23/33.45  # Initial clauses in saturation        : 28
% 33.23/33.45  # Processed clauses                    : 28260
% 33.23/33.45  # ...of these trivial                  : 2411
% 33.23/33.45  # ...subsumed                          : 23302
% 33.23/33.45  # ...remaining for further processing  : 2547
% 33.23/33.45  # Other redundant clauses eliminated   : 5
% 33.23/33.45  # Clauses deleted for lack of memory   : 0
% 33.23/33.45  # Backward-subsumed                    : 18
% 33.23/33.45  # Backward-rewritten                   : 1232
% 33.23/33.45  # Generated clauses                    : 833435
% 33.23/33.45  # ...of the previous two non-trivial   : 788187
% 33.23/33.45  # Contextual simplify-reflections      : 2
% 33.23/33.45  # Paramodulations                      : 833381
% 33.23/33.45  # Factorizations                       : 44
% 33.23/33.45  # Equation resolutions                 : 5
% 33.23/33.45  # Propositional unsat checks           : 0
% 33.23/33.45  #    Propositional check models        : 0
% 33.23/33.45  #    Propositional check unsatisfiable : 0
% 33.23/33.45  #    Propositional clauses             : 0
% 33.23/33.45  #    Propositional clauses after purity: 0
% 33.23/33.45  #    Propositional unsat core size     : 0
% 33.23/33.45  #    Propositional preprocessing time  : 0.000
% 33.23/33.45  #    Propositional encoding time       : 0.000
% 33.23/33.45  #    Propositional solver time         : 0.000
% 33.23/33.45  #    Success case prop preproc time    : 0.000
% 33.23/33.45  #    Success case prop encoding time   : 0.000
% 33.23/33.45  #    Success case prop solver time     : 0.000
% 33.23/33.45  # Current number of processed clauses  : 1259
% 33.23/33.45  #    Positive orientable unit clauses  : 403
% 33.23/33.45  #    Positive unorientable unit clauses: 198
% 33.23/33.45  #    Negative unit clauses             : 349
% 33.23/33.45  #    Non-unit-clauses                  : 309
% 33.23/33.45  # Current number of unprocessed clauses: 759300
% 33.23/33.45  # ...number of literals in the above   : 1116711
% 33.23/33.45  # Current number of archived formulas  : 0
% 33.23/33.45  # Current number of archived clauses   : 1292
% 33.23/33.45  # Clause-clause subsumption calls (NU) : 13521
% 33.23/33.45  # Rec. Clause-clause subsumption calls : 8710
% 33.23/33.45  # Non-unit clause-clause subsumptions  : 1646
% 33.23/33.45  # Unit Clause-clause subsumption calls : 45480
% 33.23/33.45  # Rewrite failures with RHS unbound    : 0
% 33.23/33.45  # BW rewrite match attempts            : 38430
% 33.23/33.45  # BW rewrite match successes           : 2104
% 33.23/33.45  # Condensation attempts                : 0
% 33.23/33.45  # Condensation successes               : 0
% 33.23/33.45  # Termbank termtop insertions          : 29871332
% 33.34/33.50  
% 33.34/33.50  # -------------------------------------------------
% 33.34/33.50  # User time                : 32.583 s
% 33.34/33.50  # System time              : 0.576 s
% 33.34/33.50  # Total time               : 33.159 s
% 33.34/33.50  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
