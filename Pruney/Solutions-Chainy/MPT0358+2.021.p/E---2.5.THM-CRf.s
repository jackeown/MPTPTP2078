%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:53 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 645 expanded)
%              Number of clauses        :   53 ( 293 expanded)
%              Number of leaves         :   15 ( 157 expanded)
%              Depth                    :   19
%              Number of atoms          :  214 (1669 expanded)
%              Number of equality atoms :   70 ( 519 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

fof(c_0_16,plain,(
    ! [X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(X45))
      | m1_subset_1(k3_subset_1(X45,X46),k1_zfmisc_1(X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & ( ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
      | esk6_0 != k1_subset_1(esk5_0) )
    & ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
      | esk6_0 = k1_subset_1(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( ~ r2_hidden(X35,X34)
        | r1_tarski(X35,X33)
        | X34 != k1_zfmisc_1(X33) )
      & ( ~ r1_tarski(X36,X33)
        | r2_hidden(X36,X34)
        | X34 != k1_zfmisc_1(X33) )
      & ( ~ r2_hidden(esk4_2(X37,X38),X38)
        | ~ r1_tarski(esk4_2(X37,X38),X37)
        | X38 = k1_zfmisc_1(X37) )
      & ( r2_hidden(esk4_2(X37,X38),X38)
        | r1_tarski(esk4_2(X37,X38),X37)
        | X38 = k1_zfmisc_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_19,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X41,X40)
        | r2_hidden(X41,X40)
        | v1_xboole_0(X40) )
      & ( ~ r2_hidden(X41,X40)
        | m1_subset_1(X41,X40)
        | v1_xboole_0(X40) )
      & ( ~ m1_subset_1(X41,X40)
        | v1_xboole_0(X41)
        | ~ v1_xboole_0(X40) )
      & ( ~ v1_xboole_0(X41)
        | m1_subset_1(X41,X40)
        | ~ v1_xboole_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X47] : ~ v1_xboole_0(k1_zfmisc_1(X47)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X27,X28] :
      ( ( k4_xboole_0(X27,X28) != k1_xboole_0
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | k4_xboole_0(X27,X28) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_28,plain,(
    ! [X29,X30] : k4_xboole_0(X29,X30) = k5_xboole_0(X29,k3_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_29,plain,(
    ! [X31,X32] :
      ( ~ r1_tarski(X31,X32)
      | k3_xboole_0(X31,X32) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

fof(c_0_32,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_33,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | k3_subset_1(X43,X44) = k4_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_34,plain,(
    ! [X48,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(X48))
      | k3_subset_1(X48,k3_subset_1(X48,X49)) = X49 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_subset_1(esk5_0,esk6_0)) = k3_subset_1(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_44,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( k3_subset_1(esk5_0,k3_subset_1(esk5_0,esk6_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_21])).

fof(c_0_46,plain,(
    ! [X42] : k1_subset_1(X42) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk5_0,k3_subset_1(esk5_0,esk6_0))
    | k5_xboole_0(esk5_0,k3_subset_1(esk5_0,esk6_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_subset_1(esk5_0,esk6_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_25]),c_0_43]),c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 = k1_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk5_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 != k1_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | r1_tarski(esk5_0,k3_subset_1(esk5_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | r1_tarski(k3_subset_1(esk5_0,k1_xboole_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_26])).

cnf(c_0_57,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_subset_1(esk5_0,k1_xboole_0)) = esk5_0
    | r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_subset_1(esk5_0,k1_xboole_0)) = k3_subset_1(esk5_0,k1_xboole_0)
    | r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_55]),c_0_39])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_56])).

fof(c_0_61,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( r2_hidden(X19,X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | ~ r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X22)
        | X23 = k4_xboole_0(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X22)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( k3_subset_1(esk5_0,k1_xboole_0) = esk5_0
    | r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | r1_tarski(k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_52])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

fof(c_0_67,plain,(
    ! [X25] :
      ( X25 = k1_xboole_0
      | r2_hidden(esk3_1(X25),X25) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_68,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_65,c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_66])])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_71,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk6_0),k5_xboole_0(X1,k3_xboole_0(X1,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk5_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_60])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( k3_xboole_0(esk6_0,k3_subset_1(esk5_0,esk6_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk6_0),k5_xboole_0(X1,k3_xboole_0(esk6_0,X1))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_39])).

cnf(c_0_80,negated_conjecture,
    ( k5_xboole_0(esk5_0,esk6_0) = k3_subset_1(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_21]),c_0_39]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(X1,k3_subset_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk6_0),k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_76]),c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_73]),c_0_82]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.19/0.43  # and selection function SelectCQIArEqFirst.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.042 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 0.19/0.43  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.43  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.43  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.43  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.43  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.43  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.43  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.43  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.43  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.43  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.43  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.19/0.43  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.43  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.43  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.43  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 0.19/0.43  fof(c_0_16, plain, ![X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(X45))|m1_subset_1(k3_subset_1(X45,X46),k1_zfmisc_1(X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.43  fof(c_0_17, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&((~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_subset_1(esk5_0))&(r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0=k1_subset_1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.43  fof(c_0_18, plain, ![X33, X34, X35, X36, X37, X38]:(((~r2_hidden(X35,X34)|r1_tarski(X35,X33)|X34!=k1_zfmisc_1(X33))&(~r1_tarski(X36,X33)|r2_hidden(X36,X34)|X34!=k1_zfmisc_1(X33)))&((~r2_hidden(esk4_2(X37,X38),X38)|~r1_tarski(esk4_2(X37,X38),X37)|X38=k1_zfmisc_1(X37))&(r2_hidden(esk4_2(X37,X38),X38)|r1_tarski(esk4_2(X37,X38),X37)|X38=k1_zfmisc_1(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.43  fof(c_0_19, plain, ![X40, X41]:(((~m1_subset_1(X41,X40)|r2_hidden(X41,X40)|v1_xboole_0(X40))&(~r2_hidden(X41,X40)|m1_subset_1(X41,X40)|v1_xboole_0(X40)))&((~m1_subset_1(X41,X40)|v1_xboole_0(X41)|~v1_xboole_0(X40))&(~v1_xboole_0(X41)|m1_subset_1(X41,X40)|~v1_xboole_0(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.43  cnf(c_0_20, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.43  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.43  fof(c_0_22, plain, ![X47]:~v1_xboole_0(k1_zfmisc_1(X47)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.43  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_24, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.43  cnf(c_0_25, negated_conjecture, (m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.43  cnf(c_0_26, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.43  fof(c_0_27, plain, ![X27, X28]:((k4_xboole_0(X27,X28)!=k1_xboole_0|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|k4_xboole_0(X27,X28)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.43  fof(c_0_28, plain, ![X29, X30]:k4_xboole_0(X29,X30)=k5_xboole_0(X29,k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.43  fof(c_0_29, plain, ![X31, X32]:(~r1_tarski(X31,X32)|k3_xboole_0(X31,X32)=X31), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.43  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_23])).
% 0.19/0.43  cnf(c_0_31, negated_conjecture, (r2_hidden(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.19/0.43  fof(c_0_32, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.43  fof(c_0_33, plain, ![X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|k3_subset_1(X43,X44)=k4_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.43  fof(c_0_34, plain, ![X48, X49]:(~m1_subset_1(X49,k1_zfmisc_1(X48))|k3_subset_1(X48,k3_subset_1(X48,X49))=X49), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.43  cnf(c_0_35, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.43  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.43  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.43  cnf(c_0_38, negated_conjecture, (r1_tarski(k3_subset_1(esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.43  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  cnf(c_0_40, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  cnf(c_0_41, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.43  cnf(c_0_42, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.43  cnf(c_0_43, negated_conjecture, (k3_xboole_0(esk5_0,k3_subset_1(esk5_0,esk6_0))=k3_subset_1(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.19/0.43  cnf(c_0_44, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_40, c_0_36])).
% 0.19/0.43  cnf(c_0_45, negated_conjecture, (k3_subset_1(esk5_0,k3_subset_1(esk5_0,esk6_0))=esk6_0), inference(spm,[status(thm)],[c_0_41, c_0_21])).
% 0.19/0.43  fof(c_0_46, plain, ![X42]:k1_subset_1(X42)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.19/0.43  cnf(c_0_47, negated_conjecture, (r1_tarski(esk5_0,k3_subset_1(esk5_0,esk6_0))|k5_xboole_0(esk5_0,k3_subset_1(esk5_0,esk6_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.43  cnf(c_0_48, negated_conjecture, (k5_xboole_0(esk5_0,k3_subset_1(esk5_0,esk6_0))=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_25]), c_0_43]), c_0_45])).
% 0.19/0.43  cnf(c_0_49, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0=k1_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.43  cnf(c_0_50, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.43  cnf(c_0_51, negated_conjecture, (r1_tarski(esk5_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.43  cnf(c_0_52, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.43  cnf(c_0_53, negated_conjecture, (~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.43  cnf(c_0_54, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|r1_tarski(esk5_0,k3_subset_1(esk5_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.43  cnf(c_0_55, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|r1_tarski(k3_subset_1(esk5_0,k1_xboole_0),esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_52])).
% 0.19/0.43  cnf(c_0_56, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_26])).
% 0.19/0.43  cnf(c_0_57, negated_conjecture, (esk6_0!=k1_xboole_0|~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_53, c_0_50])).
% 0.19/0.43  cnf(c_0_58, negated_conjecture, (k3_xboole_0(esk5_0,k3_subset_1(esk5_0,k1_xboole_0))=esk5_0|r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_54])).
% 0.19/0.43  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk5_0,k3_subset_1(esk5_0,k1_xboole_0))=k3_subset_1(esk5_0,k1_xboole_0)|r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_55]), c_0_39])).
% 0.19/0.43  cnf(c_0_60, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_56])).
% 0.19/0.43  fof(c_0_61, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk2_3(X21,X22,X23),X23)|(~r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk2_3(X21,X22,X23),X22)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.43  cnf(c_0_62, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|~r1_tarski(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_57, c_0_52])).
% 0.19/0.43  cnf(c_0_63, negated_conjecture, (k3_subset_1(esk5_0,k1_xboole_0)=esk5_0|r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.43  cnf(c_0_64, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|r1_tarski(k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_52])).
% 0.19/0.43  cnf(c_0_65, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.43  cnf(c_0_66, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.19/0.43  fof(c_0_67, plain, ![X25]:(X25=k1_xboole_0|r2_hidden(esk3_1(X25),X25)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.43  cnf(c_0_68, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_65, c_0_36])).
% 0.19/0.43  cnf(c_0_69, negated_conjecture, (esk6_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_66])])).
% 0.19/0.43  cnf(c_0_70, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.43  fof(c_0_71, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.43  cnf(c_0_72, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_68])).
% 0.19/0.43  cnf(c_0_73, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.43  cnf(c_0_74, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.43  cnf(c_0_75, negated_conjecture, (~r2_hidden(esk3_1(esk6_0),k5_xboole_0(X1,k3_xboole_0(X1,esk6_0)))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.43  cnf(c_0_76, negated_conjecture, (k3_xboole_0(esk6_0,esk5_0)=esk6_0), inference(spm,[status(thm)],[c_0_37, c_0_60])).
% 0.19/0.43  cnf(c_0_77, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_74])).
% 0.19/0.43  cnf(c_0_78, negated_conjecture, (k3_xboole_0(esk6_0,k3_subset_1(esk5_0,esk6_0))=esk6_0), inference(spm,[status(thm)],[c_0_37, c_0_66])).
% 0.19/0.43  cnf(c_0_79, negated_conjecture, (~r2_hidden(esk3_1(esk6_0),k5_xboole_0(X1,k3_xboole_0(esk6_0,X1)))), inference(spm,[status(thm)],[c_0_75, c_0_39])).
% 0.19/0.43  cnf(c_0_80, negated_conjecture, (k5_xboole_0(esk5_0,esk6_0)=k3_subset_1(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_21]), c_0_39]), c_0_76])).
% 0.19/0.43  cnf(c_0_81, negated_conjecture, (r2_hidden(X1,k3_subset_1(esk5_0,esk6_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.43  cnf(c_0_82, negated_conjecture, (~r2_hidden(esk3_1(esk6_0),k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_76]), c_0_80])).
% 0.19/0.43  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_73]), c_0_82]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 84
% 0.19/0.43  # Proof object clause steps            : 53
% 0.19/0.43  # Proof object formula steps           : 31
% 0.19/0.43  # Proof object conjectures             : 36
% 0.19/0.43  # Proof object clause conjectures      : 33
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 17
% 0.19/0.43  # Proof object initial formulas used   : 15
% 0.19/0.43  # Proof object generating inferences   : 26
% 0.19/0.43  # Proof object simplifying inferences  : 22
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 15
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 34
% 0.19/0.43  # Removed in clause preprocessing      : 2
% 0.19/0.43  # Initial clauses in saturation        : 32
% 0.19/0.43  # Processed clauses                    : 271
% 0.19/0.43  # ...of these trivial                  : 15
% 0.19/0.43  # ...subsumed                          : 64
% 0.19/0.43  # ...remaining for further processing  : 192
% 0.19/0.43  # Other redundant clauses eliminated   : 13
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 12
% 0.19/0.43  # Backward-rewritten                   : 43
% 0.19/0.43  # Generated clauses                    : 2178
% 0.19/0.43  # ...of the previous two non-trivial   : 1893
% 0.19/0.43  # Contextual simplify-reflections      : 1
% 0.19/0.43  # Paramodulations                      : 2165
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 13
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 97
% 0.19/0.43  #    Positive orientable unit clauses  : 27
% 0.19/0.43  #    Positive unorientable unit clauses: 1
% 0.19/0.43  #    Negative unit clauses             : 18
% 0.19/0.43  #    Non-unit-clauses                  : 51
% 0.19/0.43  # Current number of unprocessed clauses: 1635
% 0.19/0.43  # ...number of literals in the above   : 5123
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 89
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 1573
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 1245
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 46
% 0.19/0.43  # Unit Clause-clause subsumption calls : 273
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 12
% 0.19/0.43  # BW rewrite match successes           : 8
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 27013
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.093 s
% 0.19/0.43  # System time              : 0.006 s
% 0.19/0.43  # Total time               : 0.098 s
% 0.19/0.43  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
