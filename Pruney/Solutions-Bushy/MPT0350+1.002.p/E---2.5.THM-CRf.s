%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0350+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:28 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 639 expanded)
%              Number of clauses        :   34 ( 274 expanded)
%              Number of leaves         :   12 ( 153 expanded)
%              Depth                    :   14
%              Number of atoms          :  125 (1501 expanded)
%              Number of equality atoms :   42 ( 468 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

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

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X15] : k2_subset_1(X15) = X15 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_15,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | k4_subset_1(X20,X21,X22) = k2_xboole_0(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_18,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | X26 = k2_xboole_0(X25,k4_xboole_0(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_19,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | k3_subset_1(X16,X17) = k4_xboole_0(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_20,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k2_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)) != esk2_0
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k3_subset_1(X2,X1)) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_27,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | m1_subset_1(k3_subset_1(X18,X19),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_28,plain,(
    ! [X6,X7,X8,X9,X10,X11] :
      ( ( ~ r2_hidden(X8,X7)
        | r1_tarski(X8,X6)
        | X7 != k1_zfmisc_1(X6) )
      & ( ~ r1_tarski(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k1_zfmisc_1(X6) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | ~ r1_tarski(esk1_2(X10,X11),X10)
        | X11 = k1_zfmisc_1(X10) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(esk1_2(X10,X11),X10)
        | X11 = k1_zfmisc_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_29,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X14,X13)
        | r2_hidden(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ r2_hidden(X14,X13)
        | m1_subset_1(X14,X13)
        | v1_xboole_0(X13) )
      & ( ~ m1_subset_1(X14,X13)
        | v1_xboole_0(X14)
        | ~ v1_xboole_0(X13) )
      & ( ~ v1_xboole_0(X14)
        | m1_subset_1(X14,X13)
        | ~ v1_xboole_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_22])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_22])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk2_0))
    | r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_39,plain,(
    ! [X27] :
      ( ~ v1_xboole_0(X27)
      | X27 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_42,plain,(
    ! [X23] : k2_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_43,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_44,plain,(
    ! [X24] : k4_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k1_zfmisc_1(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( k3_subset_1(esk2_0,k1_xboole_0) != esk2_0
    | ~ m1_subset_1(k3_subset_1(esk2_0,k1_xboole_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_50]),c_0_51])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_53]),c_0_50]),c_0_55])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_50]),c_0_55])]),c_0_57]),
    [proof]).

%------------------------------------------------------------------------------
