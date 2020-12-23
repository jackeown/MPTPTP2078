%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  119 (1689 expanded)
%              Number of clauses        :   76 ( 785 expanded)
%              Number of leaves         :   21 ( 448 expanded)
%              Depth                    :   16
%              Number of atoms          :  202 (2787 expanded)
%              Number of equality atoms :   97 (1596 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_21,plain,(
    ! [X39,X40] :
      ( ( ~ m1_subset_1(X40,X39)
        | r2_hidden(X40,X39)
        | v1_xboole_0(X39) )
      & ( ~ r2_hidden(X40,X39)
        | m1_subset_1(X40,X39)
        | v1_xboole_0(X39) )
      & ( ~ m1_subset_1(X40,X39)
        | v1_xboole_0(X40)
        | ~ v1_xboole_0(X39) )
      & ( ~ v1_xboole_0(X40)
        | m1_subset_1(X40,X39)
        | ~ v1_xboole_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_22,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X44))
      | m1_subset_1(k3_subset_1(X44,X45),k1_zfmisc_1(X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_23,plain,(
    ! [X46] : ~ v1_xboole_0(k1_zfmisc_1(X46)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_24,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | k3_subset_1(X42,X43) = k4_xboole_0(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_25,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_26,plain,(
    ! [X37,X38] : k3_tarski(k2_tarski(X37,X38)) = k2_xboole_0(X37,X38) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_28,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_29,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ( ~ r2_hidden(X32,X31)
        | r1_tarski(X32,X30)
        | X31 != k1_zfmisc_1(X30) )
      & ( ~ r1_tarski(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k1_zfmisc_1(X30) )
      & ( ~ r2_hidden(esk1_2(X34,X35),X35)
        | ~ r1_tarski(esk1_2(X34,X35),X34)
        | X35 = k1_zfmisc_1(X34) )
      & ( r2_hidden(esk1_2(X34,X35),X35)
        | r1_tarski(esk1_2(X34,X35),X34)
        | X35 = k1_zfmisc_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X13,X14] : k2_xboole_0(X13,k3_xboole_0(X13,X14)) = X13 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_36,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_38,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_39,plain,(
    ! [X23,X24] : k2_xboole_0(X23,X24) = k5_xboole_0(X23,k4_xboole_0(X24,X23)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_40,plain,(
    ! [X10,X11,X12] : k5_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X12,X11)) = k3_xboole_0(k5_xboole_0(X10,X12),X11) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_41,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_42,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_49,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k2_xboole_0(X17,X18)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_52,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_54,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_60,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_32])).

cnf(c_0_61,plain,
    ( k3_subset_1(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_46]),c_0_32])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_65,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_51]),c_0_34]),c_0_52])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_69,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,plain,
    ( k3_subset_1(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_51]),c_0_34]),c_0_52])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_74,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

cnf(c_0_75,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_62])).

cnf(c_0_76,plain,
    ( k3_subset_1(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_58]),c_0_68])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_71,c_0_65])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

fof(c_0_79,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_74])])])).

cnf(c_0_80,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_58])])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_56]),c_0_68])).

fof(c_0_82,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(X47))
      | ~ m1_subset_1(X49,k1_zfmisc_1(X47))
      | k4_subset_1(X47,X48,X49) = k2_xboole_0(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_83]),c_0_32])).

fof(c_0_87,plain,(
    ! [X20,X21,X22] : k5_xboole_0(k5_xboole_0(X20,X21),X22) = k5_xboole_0(X20,k5_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_88,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_89,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_81])).

cnf(c_0_90,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_55])).

cnf(c_0_91,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_enumset1(X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_51]),c_0_52])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_86])).

cnf(c_0_93,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_94,plain,
    ( X1 = k5_xboole_0(X2,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,plain,
    ( r1_tarski(k3_xboole_0(X1,k5_xboole_0(X2,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

fof(c_0_96,plain,(
    ! [X41] : k2_subset_1(X41) = X41 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_97,plain,
    ( k4_subset_1(X1,X2,X3) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_91,c_0_65])).

cnf(c_0_98,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_92]),c_0_66])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_93,c_0_56])).

cnf(c_0_100,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,X2)) = k5_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_102,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_103,plain,
    ( k4_subset_1(X1,X2,X3) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X3,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_46]),c_0_32])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_83])).

cnf(c_0_105,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_83]),c_0_98])).

cnf(c_0_106,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X2,k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_81])).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X3,X3))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_56])).

cnf(c_0_108,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_109,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,X1) = k5_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_83])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(k5_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_111,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_100]),c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_108,c_0_105])).

cnf(c_0_113,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0)) = k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_55]),c_0_98]),c_0_68]),c_0_81]),c_0_93]),c_0_56])).

cnf(c_0_114,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_106,c_0_111])).

cnf(c_0_115,plain,
    ( k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_81])).

cnf(c_0_116,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_117,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_56])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_117])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:19:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.014 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.38  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.38  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.38  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.19/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.38  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 0.19/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.38  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.38  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 0.19/0.38  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.19/0.38  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.38  fof(c_0_21, plain, ![X39, X40]:(((~m1_subset_1(X40,X39)|r2_hidden(X40,X39)|v1_xboole_0(X39))&(~r2_hidden(X40,X39)|m1_subset_1(X40,X39)|v1_xboole_0(X39)))&((~m1_subset_1(X40,X39)|v1_xboole_0(X40)|~v1_xboole_0(X39))&(~v1_xboole_0(X40)|m1_subset_1(X40,X39)|~v1_xboole_0(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.38  fof(c_0_22, plain, ![X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(X44))|m1_subset_1(k3_subset_1(X44,X45),k1_zfmisc_1(X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.38  fof(c_0_23, plain, ![X46]:~v1_xboole_0(k1_zfmisc_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.38  fof(c_0_24, plain, ![X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|k3_subset_1(X42,X43)=k4_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.38  fof(c_0_25, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.38  fof(c_0_26, plain, ![X37, X38]:k3_tarski(k2_tarski(X37,X38))=k2_xboole_0(X37,X38), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.38  fof(c_0_27, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  fof(c_0_28, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  fof(c_0_29, plain, ![X30, X31, X32, X33, X34, X35]:(((~r2_hidden(X32,X31)|r1_tarski(X32,X30)|X31!=k1_zfmisc_1(X30))&(~r1_tarski(X33,X30)|r2_hidden(X33,X31)|X31!=k1_zfmisc_1(X30)))&((~r2_hidden(esk1_2(X34,X35),X35)|~r1_tarski(esk1_2(X34,X35),X34)|X35=k1_zfmisc_1(X34))&(r2_hidden(esk1_2(X34,X35),X35)|r1_tarski(esk1_2(X34,X35),X34)|X35=k1_zfmisc_1(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.38  cnf(c_0_30, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_31, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_32, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_33, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  fof(c_0_35, plain, ![X13, X14]:k2_xboole_0(X13,k3_xboole_0(X13,X14))=X13, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.19/0.38  cnf(c_0_36, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  fof(c_0_38, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_39, plain, ![X23, X24]:k2_xboole_0(X23,X24)=k5_xboole_0(X23,k4_xboole_0(X24,X23)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.38  fof(c_0_40, plain, ![X10, X11, X12]:k5_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X12,X11))=k3_xboole_0(k5_xboole_0(X10,X12),X11), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 0.19/0.38  fof(c_0_41, plain, ![X19]:k5_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.38  fof(c_0_42, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.38  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_44, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_45, plain, (r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.19/0.38  cnf(c_0_46, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_47, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.38  cnf(c_0_48, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  fof(c_0_49, plain, ![X17, X18]:k4_xboole_0(X17,k2_xboole_0(X17,X18))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.38  cnf(c_0_50, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_51, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.38  cnf(c_0_52, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_53, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  fof(c_0_54, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.38  cnf(c_0_55, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.38  cnf(c_0_57, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_58, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_44])).
% 0.19/0.38  cnf(c_0_60, plain, (r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_32])).
% 0.19/0.38  cnf(c_0_61, plain, (k3_subset_1(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_46]), c_0_32])).
% 0.19/0.38  cnf(c_0_62, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_48])).
% 0.19/0.38  cnf(c_0_63, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.38  cnf(c_0_64, plain, (k3_tarski(k2_enumset1(X1,X1,X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.19/0.38  cnf(c_0_65, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_51]), c_0_34]), c_0_52])).
% 0.19/0.38  cnf(c_0_66, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.38  cnf(c_0_67, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.38  cnf(c_0_68, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.38  cnf(c_0_69, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.38  cnf(c_0_70, plain, (k3_subset_1(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.38  cnf(c_0_71, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_51]), c_0_34]), c_0_52])).
% 0.19/0.38  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.19/0.38  cnf(c_0_73, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.38  fof(c_0_74, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.19/0.38  cnf(c_0_75, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_69, c_0_62])).
% 0.19/0.38  cnf(c_0_76, plain, (k3_subset_1(X1,X1)=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_58]), c_0_68])).
% 0.19/0.38  cnf(c_0_77, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_71, c_0_65])).
% 0.19/0.38  cnf(c_0_78, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.38  fof(c_0_79, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_74])])])).
% 0.19/0.38  cnf(c_0_80, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_58])])).
% 0.19/0.38  cnf(c_0_81, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_56]), c_0_68])).
% 0.19/0.38  fof(c_0_82, plain, ![X47, X48, X49]:(~m1_subset_1(X48,k1_zfmisc_1(X47))|~m1_subset_1(X49,k1_zfmisc_1(X47))|k4_subset_1(X47,X48,X49)=k2_xboole_0(X48,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.19/0.38  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.38  cnf(c_0_84, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.38  cnf(c_0_85, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.19/0.38  cnf(c_0_86, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_83]), c_0_32])).
% 0.19/0.38  fof(c_0_87, plain, ![X20, X21, X22]:k5_xboole_0(k5_xboole_0(X20,X21),X22)=k5_xboole_0(X20,k5_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.38  cnf(c_0_88, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_89, plain, (r1_tarski(k5_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_84, c_0_81])).
% 0.19/0.38  cnf(c_0_90, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(X2,k5_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_66, c_0_55])).
% 0.19/0.38  cnf(c_0_91, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_enumset1(X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_51]), c_0_52])).
% 0.19/0.38  cnf(c_0_92, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_59, c_0_86])).
% 0.19/0.38  cnf(c_0_93, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.38  cnf(c_0_94, plain, (X1=k5_xboole_0(X2,X2)|~r1_tarski(X1,k5_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.38  cnf(c_0_95, plain, (r1_tarski(k3_xboole_0(X1,k5_xboole_0(X2,X2)),X3)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.19/0.38  fof(c_0_96, plain, ![X41]:k2_subset_1(X41)=X41, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.38  cnf(c_0_97, plain, (k4_subset_1(X1,X2,X3)=k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_91, c_0_65])).
% 0.19/0.38  cnf(c_0_98, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_92]), c_0_66])).
% 0.19/0.38  cnf(c_0_99, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_93, c_0_56])).
% 0.19/0.38  cnf(c_0_100, plain, (k3_xboole_0(X1,k5_xboole_0(X2,X2))=k5_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.38  cnf(c_0_101, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.38  cnf(c_0_102, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.19/0.38  cnf(c_0_103, plain, (k4_subset_1(X1,X2,X3)=k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r2_hidden(X3,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_46]), c_0_32])).
% 0.19/0.38  cnf(c_0_104, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_45, c_0_83])).
% 0.19/0.38  cnf(c_0_105, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_83]), c_0_98])).
% 0.19/0.38  cnf(c_0_106, plain, (k5_xboole_0(k1_xboole_0,X1)=k5_xboole_0(X2,k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_93, c_0_81])).
% 0.19/0.38  cnf(c_0_107, plain, (k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X3,X3)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_56])).
% 0.19/0.38  cnf(c_0_108, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_101, c_0_102])).
% 0.19/0.38  cnf(c_0_109, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,X1)=k5_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))|~r2_hidden(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_103, c_0_83])).
% 0.19/0.38  cnf(c_0_110, negated_conjecture, (r2_hidden(k5_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[c_0_104, c_0_105])).
% 0.19/0.38  cnf(c_0_111, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_100]), c_0_107])).
% 0.19/0.38  cnf(c_0_112, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_108, c_0_105])).
% 0.19/0.38  cnf(c_0_113, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0))=k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_55]), c_0_98]), c_0_68]), c_0_81]), c_0_93]), c_0_56])).
% 0.19/0.38  cnf(c_0_114, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_106, c_0_111])).
% 0.19/0.38  cnf(c_0_115, plain, (k1_xboole_0=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_93, c_0_81])).
% 0.19/0.38  cnf(c_0_116, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_112, c_0_113])).
% 0.19/0.38  cnf(c_0_117, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_56])).
% 0.19/0.38  cnf(c_0_118, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_117])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 119
% 0.19/0.38  # Proof object clause steps            : 76
% 0.19/0.38  # Proof object formula steps           : 43
% 0.19/0.38  # Proof object conjectures             : 17
% 0.19/0.38  # Proof object clause conjectures      : 14
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 25
% 0.19/0.38  # Proof object initial formulas used   : 21
% 0.19/0.38  # Proof object generating inferences   : 33
% 0.19/0.38  # Proof object simplifying inferences  : 47
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 21
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 30
% 0.19/0.38  # Removed in clause preprocessing      : 5
% 0.19/0.38  # Initial clauses in saturation        : 25
% 0.19/0.38  # Processed clauses                    : 489
% 0.19/0.38  # ...of these trivial                  : 61
% 0.19/0.38  # ...subsumed                          : 199
% 0.19/0.38  # ...remaining for further processing  : 229
% 0.19/0.38  # Other redundant clauses eliminated   : 4
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 7
% 0.19/0.38  # Backward-rewritten                   : 60
% 0.19/0.38  # Generated clauses                    : 3130
% 0.19/0.38  # ...of the previous two non-trivial   : 2389
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 3124
% 0.19/0.38  # Factorizations                       : 2
% 0.19/0.38  # Equation resolutions                 : 4
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 134
% 0.19/0.38  #    Positive orientable unit clauses  : 63
% 0.19/0.38  #    Positive unorientable unit clauses: 13
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 57
% 0.19/0.38  # Current number of unprocessed clauses: 1874
% 0.19/0.38  # ...number of literals in the above   : 2224
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 96
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 949
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 739
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 47
% 0.19/0.38  # Unit Clause-clause subsumption calls : 688
% 0.19/0.38  # Rewrite failures with RHS unbound    : 100
% 0.19/0.38  # BW rewrite match attempts            : 605
% 0.19/0.38  # BW rewrite match successes           : 78
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 46055
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.033 s
% 0.19/0.38  # System time              : 0.010 s
% 0.19/0.38  # Total time               : 0.043 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
