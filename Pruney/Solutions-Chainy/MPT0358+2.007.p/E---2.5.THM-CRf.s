%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:51 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 558 expanded)
%              Number of clauses        :   48 ( 275 expanded)
%              Number of leaves         :   12 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :  169 (1416 expanded)
%              Number of equality atoms :   65 ( 589 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(c_0_12,plain,(
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

fof(c_0_13,plain,(
    ! [X29,X30] : k4_xboole_0(X29,X30) = k5_xboole_0(X29,k3_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X38,X39] : k2_xboole_0(X38,X39) = k5_xboole_0(X38,k4_xboole_0(X39,X38)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_17,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,plain,(
    ! [X34,X35] :
      ( ~ r1_tarski(X34,X35)
      | k3_xboole_0(X34,X35) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_19,plain,(
    ! [X31,X32,X33] :
      ( ( r1_tarski(X31,X32)
        | ~ r1_tarski(X31,k4_xboole_0(X32,X33)) )
      & ( r1_xboole_0(X31,X33)
        | ~ r1_tarski(X31,k4_xboole_0(X32,X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_20,plain,(
    ! [X36,X37] : k4_xboole_0(X36,k2_xboole_0(X36,X37)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X25] :
      ( X25 = k1_xboole_0
      | r2_hidden(esk3_1(X25),X25) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_15])).

fof(c_0_29,plain,(
    ! [X27,X28] :
      ( ( r1_tarski(X27,X28)
        | X27 != X28 )
      & ( r1_tarski(X28,X27)
        | X27 != X28 )
      & ( ~ r1_tarski(X27,X28)
        | ~ r1_tarski(X28,X27)
        | X27 = X28 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_22,c_0_15])).

fof(c_0_31,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_32,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,k5_xboole_0(X1,X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_15])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_15]),c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_1(k5_xboole_0(X1,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_15])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r2_hidden(esk3_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | r2_hidden(esk3_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_33])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_39])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_49,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

fof(c_0_50,plain,(
    ! [X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(X50))
      | k3_subset_1(X50,X51) = k4_xboole_0(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,k5_xboole_0(X2,X1))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_46])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_55,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & ( ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
      | esk6_0 != k1_subset_1(esk5_0) )
    & ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
      | esk6_0 = k1_subset_1(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_49])])])).

fof(c_0_56,plain,(
    ! [X49] : k1_subset_1(X49) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_57,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | r2_hidden(esk3_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_33])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_24]),c_0_42])])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_48])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 = k1_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_15])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_24]),c_0_59]),c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 != k1_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k3_subset_1(X2,X1))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_1(esk6_0),k3_subset_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_70,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])]),c_0_33])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_71]),c_0_71]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:26:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.50  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.028 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.50  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.50  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.50  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.50  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.19/0.50  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.50  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.50  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.50  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 0.19/0.50  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.50  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.19/0.50  fof(c_0_12, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk2_3(X21,X22,X23),X23)|(~r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk2_3(X21,X22,X23),X22)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.50  fof(c_0_13, plain, ![X29, X30]:k4_xboole_0(X29,X30)=k5_xboole_0(X29,k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.50  cnf(c_0_14, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.50  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.50  fof(c_0_16, plain, ![X38, X39]:k2_xboole_0(X38,X39)=k5_xboole_0(X38,k4_xboole_0(X39,X38)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.50  cnf(c_0_17, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.50  fof(c_0_18, plain, ![X34, X35]:(~r1_tarski(X34,X35)|k3_xboole_0(X34,X35)=X34), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.50  fof(c_0_19, plain, ![X31, X32, X33]:((r1_tarski(X31,X32)|~r1_tarski(X31,k4_xboole_0(X32,X33)))&(r1_xboole_0(X31,X33)|~r1_tarski(X31,k4_xboole_0(X32,X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.19/0.50  fof(c_0_20, plain, ![X36, X37]:k4_xboole_0(X36,k2_xboole_0(X36,X37))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.50  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.50  cnf(c_0_23, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.50  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.50  fof(c_0_25, plain, ![X25]:(X25=k1_xboole_0|r2_hidden(esk3_1(X25),X25)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.50  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.50  cnf(c_0_27, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.50  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_21, c_0_15])).
% 0.19/0.50  fof(c_0_29, plain, ![X27, X28]:(((r1_tarski(X27,X28)|X27!=X28)&(r1_tarski(X28,X27)|X27!=X28))&(~r1_tarski(X27,X28)|~r1_tarski(X28,X27)|X27=X28)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.50  cnf(c_0_30, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_22, c_0_15])).
% 0.19/0.50  fof(c_0_31, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.50  cnf(c_0_32, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,k5_xboole_0(X1,X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.50  cnf(c_0_33, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.50  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_26, c_0_15])).
% 0.19/0.50  cnf(c_0_35, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_15]), c_0_28])).
% 0.19/0.50  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.50  cnf(c_0_37, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.50  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_30])).
% 0.19/0.50  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.50  cnf(c_0_40, plain, (k5_xboole_0(X1,X1)=k1_xboole_0|~r1_tarski(X1,X2)|~r2_hidden(esk3_1(k5_xboole_0(X1,X1)),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.50  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.50  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.19/0.50  cnf(c_0_43, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_15])).
% 0.19/0.50  cnf(c_0_44, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r2_hidden(esk3_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 0.19/0.50  cnf(c_0_45, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|r2_hidden(esk3_1(k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_38, c_0_33])).
% 0.19/0.50  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_39])).
% 0.19/0.50  cnf(c_0_47, plain, (k5_xboole_0(X1,X1)=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_40, c_0_33])).
% 0.19/0.50  cnf(c_0_48, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.50  fof(c_0_49, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 0.19/0.50  fof(c_0_50, plain, ![X50, X51]:(~m1_subset_1(X51,k1_zfmisc_1(X50))|k3_subset_1(X50,X51)=k4_xboole_0(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.50  cnf(c_0_51, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_43])).
% 0.19/0.50  cnf(c_0_52, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.50  cnf(c_0_53, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,k5_xboole_0(X2,X1))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_23, c_0_46])).
% 0.19/0.50  cnf(c_0_54, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.50  fof(c_0_55, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&((~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_subset_1(esk5_0))&(r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0=k1_subset_1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_49])])])).
% 0.19/0.50  fof(c_0_56, plain, ![X49]:k1_subset_1(X49)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.19/0.50  cnf(c_0_57, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.50  cnf(c_0_58, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),k5_xboole_0(X1,k3_xboole_0(X1,X2)))|r2_hidden(esk3_1(X1),X2)), inference(spm,[status(thm)],[c_0_51, c_0_33])).
% 0.19/0.50  cnf(c_0_59, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_24]), c_0_42])])).
% 0.19/0.50  cnf(c_0_60, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_48])])).
% 0.19/0.50  cnf(c_0_61, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0=k1_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.50  cnf(c_0_62, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.50  cnf(c_0_63, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_57, c_0_15])).
% 0.19/0.50  cnf(c_0_64, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X2)|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_24]), c_0_59]), c_0_60])).
% 0.19/0.50  cnf(c_0_65, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.50  cnf(c_0_66, negated_conjecture, (~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.50  cnf(c_0_67, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k3_subset_1(X2,X1))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_23, c_0_63])).
% 0.19/0.50  cnf(c_0_68, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_1(esk6_0),k3_subset_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.50  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.50  cnf(c_0_70, negated_conjecture, (esk6_0!=k1_xboole_0|~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_66, c_0_62])).
% 0.19/0.50  cnf(c_0_71, negated_conjecture, (esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])]), c_0_33])).
% 0.19/0.50  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_71]), c_0_71]), c_0_48])]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 73
% 0.19/0.50  # Proof object clause steps            : 48
% 0.19/0.50  # Proof object formula steps           : 25
% 0.19/0.50  # Proof object conjectures             : 11
% 0.19/0.50  # Proof object clause conjectures      : 8
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 16
% 0.19/0.50  # Proof object initial formulas used   : 12
% 0.19/0.50  # Proof object generating inferences   : 18
% 0.19/0.50  # Proof object simplifying inferences  : 28
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 16
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 37
% 0.19/0.50  # Removed in clause preprocessing      : 3
% 0.19/0.50  # Initial clauses in saturation        : 34
% 0.19/0.50  # Processed clauses                    : 1603
% 0.19/0.50  # ...of these trivial                  : 8
% 0.19/0.50  # ...subsumed                          : 1220
% 0.19/0.50  # ...remaining for further processing  : 375
% 0.19/0.50  # Other redundant clauses eliminated   : 12
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 9
% 0.19/0.50  # Backward-rewritten                   : 51
% 0.19/0.50  # Generated clauses                    : 8136
% 0.19/0.50  # ...of the previous two non-trivial   : 7068
% 0.19/0.50  # Contextual simplify-reflections      : 3
% 0.19/0.50  # Paramodulations                      : 8096
% 0.19/0.50  # Factorizations                       : 28
% 0.19/0.50  # Equation resolutions                 : 12
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 272
% 0.19/0.50  #    Positive orientable unit clauses  : 23
% 0.19/0.50  #    Positive unorientable unit clauses: 1
% 0.19/0.50  #    Negative unit clauses             : 3
% 0.19/0.50  #    Non-unit-clauses                  : 245
% 0.19/0.50  # Current number of unprocessed clauses: 5486
% 0.19/0.50  # ...number of literals in the above   : 19096
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 96
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 33158
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 16927
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 829
% 0.19/0.50  # Unit Clause-clause subsumption calls : 704
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 101
% 0.19/0.50  # BW rewrite match successes           : 26
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 121098
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.155 s
% 0.19/0.50  # System time              : 0.008 s
% 0.19/0.50  # Total time               : 0.162 s
% 0.19/0.50  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
