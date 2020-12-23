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
% DateTime   : Thu Dec  3 10:45:41 EST 2020

% Result     : Theorem 5.03s
% Output     : CNFRefutation 5.03s
% Verified   : 
% Statistics : Number of formulae       :  161 (16206 expanded)
%              Number of clauses        :  122 (7782 expanded)
%              Number of leaves         :   19 (4162 expanded)
%              Depth                    :   26
%              Number of atoms          :  336 (27714 expanded)
%              Number of equality atoms :   49 (10946 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

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

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t33_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(c_0_19,plain,(
    ! [X29,X30] : k2_xboole_0(X29,X30) = k5_xboole_0(X29,k4_xboole_0(X30,X29)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_20,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X16,X17,X18] :
      ( ( r1_tarski(X16,X17)
        | ~ r1_tarski(X16,k4_xboole_0(X17,X18)) )
      & ( r1_xboole_0(X16,X18)
        | ~ r1_tarski(X16,k4_xboole_0(X17,X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_22,plain,(
    ! [X25] : k4_xboole_0(k1_xboole_0,X25) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_23,plain,(
    ! [X19] : k2_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X23,X24] : r1_tarski(k4_xboole_0(X23,X24),X23) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_30,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_31,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | k3_subset_1(X40,X41) = k4_xboole_0(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_38,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(X26,X27)
      | r1_xboole_0(X26,k4_xboole_0(X28,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_39,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ( ~ r2_hidden(X33,X32)
        | r1_tarski(X33,X31)
        | X32 != k1_zfmisc_1(X31) )
      & ( ~ r1_tarski(X34,X31)
        | r2_hidden(X34,X32)
        | X32 != k1_zfmisc_1(X31) )
      & ( ~ r2_hidden(esk3_2(X35,X36),X36)
        | ~ r1_tarski(esk3_2(X35,X36),X35)
        | X36 = k1_zfmisc_1(X35) )
      & ( r2_hidden(esk3_2(X35,X36),X36)
        | r1_tarski(esk3_2(X35,X36),X35)
        | X36 = k1_zfmisc_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_40,plain,(
    ! [X38,X39] :
      ( ( ~ m1_subset_1(X39,X38)
        | r2_hidden(X39,X38)
        | v1_xboole_0(X38) )
      & ( ~ r2_hidden(X39,X38)
        | m1_subset_1(X39,X38)
        | v1_xboole_0(X38) )
      & ( ~ m1_subset_1(X39,X38)
        | v1_xboole_0(X39)
        | ~ v1_xboole_0(X38) )
      & ( ~ v1_xboole_0(X39)
        | m1_subset_1(X39,X38)
        | ~ v1_xboole_0(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_41,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))
    & ( ~ r1_tarski(esk5_0,esk6_0)
      | ~ r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) )
    & ( r1_tarski(esk5_0,esk6_0)
      | r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_42,plain,(
    ! [X44] : ~ v1_xboole_0(k1_zfmisc_1(X44)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_46,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_48,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_25])).

cnf(c_0_49,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_45,c_0_35])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_35])).

cnf(c_0_59,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_25])).

fof(c_0_60,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | r1_tarski(k4_xboole_0(X20,X22),k4_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_xboole_1])])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_50,c_0_25])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_55]),c_0_56])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_55]),c_0_56])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_68,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_55]),c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,plain,
    ( k3_subset_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = X1
    | ~ m1_subset_1(k5_xboole_0(X2,k3_xboole_0(X2,X3)),k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_66,c_0_61])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X3)),k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_25]),c_0_25])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(esk6_0,X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_71])).

cnf(c_0_78,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_55]),c_0_56]),c_0_56])).

cnf(c_0_79,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_54])).

cnf(c_0_80,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X1,X4)
    | ~ r1_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(esk6_0,k5_xboole_0(X1,k3_xboole_0(X1,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X2,X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,esk4_0)),esk6_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

fof(c_0_84,plain,(
    ! [X42,X43] : m1_subset_1(k6_subset_1(X42,X43),k1_zfmisc_1(X42)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_85,plain,(
    ! [X47,X48] : k6_subset_1(X47,X48) = k4_xboole_0(X47,X48) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_86,plain,(
    ! [X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(X45))
      | k3_subset_1(X45,k3_subset_1(X45,X46)) = X46 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_87,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ r1_tarski(X2,X1)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_71])).

cnf(c_0_88,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk4_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_70])).

cnf(c_0_89,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_90,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_91,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( k3_subset_1(esk6_0,k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk4_0))) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_48])])).

cnf(c_0_93,plain,
    ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90]),c_0_25])).

cnf(c_0_94,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_55]),c_0_56])).

cnf(c_0_95,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_77])).

cnf(c_0_96,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk4_0)) = k3_subset_1(esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])])).

cnf(c_0_97,negated_conjecture,
    ( r1_xboole_0(esk6_0,X1)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_70])).

cnf(c_0_98,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_subset_1(esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_100,negated_conjecture,
    ( r1_xboole_0(X1,esk6_0)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( k3_subset_1(esk4_0,k3_subset_1(esk6_0,esk6_0)) = esk4_0
    | ~ m1_subset_1(k3_subset_1(esk6_0,esk6_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_98])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_99,c_0_25])).

cnf(c_0_103,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_94,c_0_48])).

cnf(c_0_104,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_subset_1(X3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_75,c_0_59])).

cnf(c_0_105,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),esk6_0)
    | ~ r1_tarski(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_100,c_0_61])).

cnf(c_0_106,negated_conjecture,
    ( k3_subset_1(esk6_0,esk6_0) = k3_subset_1(esk4_0,esk4_0)
    | ~ m1_subset_1(k3_subset_1(esk6_0,esk6_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_101])).

cnf(c_0_107,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_102,c_0_75])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    | r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_110,plain,
    ( r1_xboole_0(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_103,c_0_59])).

cnf(c_0_111,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_55]),c_0_56])).

cnf(c_0_112,negated_conjecture,
    ( r1_xboole_0(X1,esk6_0)
    | ~ r1_tarski(esk4_0,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_55]),c_0_56])).

cnf(c_0_113,negated_conjecture,
    ( k3_subset_1(esk6_0,esk6_0) = k3_subset_1(esk4_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk6_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_79])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk6_0,esk6_0),X1)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_96])).

cnf(c_0_115,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_59])).

cnf(c_0_116,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_59])).

cnf(c_0_117,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_108]),c_0_54])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    | r1_xboole_0(k3_subset_1(esk4_0,esk6_0),X1)
    | ~ r1_xboole_0(k3_subset_1(esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_109])).

cnf(c_0_119,plain,
    ( r1_xboole_0(k3_subset_1(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_59])).

cnf(c_0_120,plain,
    ( r1_xboole_0(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_110])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk4_0,esk6_0))
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_xboole_0(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_53])).

cnf(c_0_122,negated_conjecture,
    ( r1_xboole_0(X1,esk6_0)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_71])).

cnf(c_0_123,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk6_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_96])).

cnf(c_0_124,negated_conjecture,
    ( k3_subset_1(esk6_0,esk6_0) = k3_subset_1(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_70])])).

cnf(c_0_125,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_91]),c_0_116])).

cnf(c_0_126,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_111,c_0_79])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_117])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    | r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_108])])).

cnf(c_0_129,negated_conjecture,
    ( r1_xboole_0(X1,k3_subset_1(esk4_0,esk6_0))
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_120,c_0_53])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk4_0,esk6_0))
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_131,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk4_0,esk4_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_132,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_53])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk4_0),X1)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(rw,[status(thm)],[c_0_114,c_0_124])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(esk5_0,k3_subset_1(esk4_0,X1))
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    | r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_128])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk6_0),esk4_0)
    | r1_tarski(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_109]),c_0_108])])).

cnf(c_0_137,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk6_0,esk6_0),k3_subset_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_98])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk4_0),k3_subset_1(esk4_0,esk6_0))
    | ~ r1_tarski(k3_subset_1(esk4_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_139,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_71])])).

cnf(c_0_140,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_61])).

cnf(c_0_141,negated_conjecture,
    ( r1_tarski(esk5_0,k3_subset_1(esk4_0,k3_subset_1(esk4_0,esk6_0)))
    | r1_tarski(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_136])).

cnf(c_0_142,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_59])).

cnf(c_0_143,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_59])).

cnf(c_0_144,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk4_0,esk4_0),k3_subset_1(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_137,c_0_124])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk4_0),k3_subset_1(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_138,c_0_139])])).

cnf(c_0_146,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_55]),c_0_56])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_91]),c_0_53])])).

cnf(c_0_148,plain,
    ( r1_xboole_0(k3_subset_1(k3_subset_1(X1,X2),X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_149,negated_conjecture,
    ( k3_subset_1(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk4_0)) = k3_subset_1(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_144]),c_0_145])])).

cnf(c_0_150,plain,
    ( r1_tarski(k3_subset_1(k3_subset_1(X1,X2),X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_143])).

cnf(c_0_151,negated_conjecture,
    ( r1_xboole_0(X1,esk5_0)
    | ~ r1_xboole_0(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_152,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk6_0)
    | ~ m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(k3_subset_1(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_53])])).

cnf(c_0_153,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk6_0),esk4_0)
    | ~ m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(k3_subset_1(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_149]),c_0_53])])).

cnf(c_0_154,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk6_0)
    | ~ r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_155,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk4_0,esk5_0))
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_108])).

cnf(c_0_156,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk5_0)
    | ~ m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(k3_subset_1(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_151,c_0_152])).

cnf(c_0_157,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_79]),c_0_145])])).

cnf(c_0_158,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154,c_0_147])])).

cnf(c_0_159,negated_conjecture,
    ( ~ m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(k3_subset_1(esk4_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_156]),c_0_157])]),c_0_158])).

cnf(c_0_160,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_79]),c_0_145])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:38:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 5.03/5.20  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 5.03/5.20  # and selection function SelectComplexExceptUniqMaxHorn.
% 5.03/5.20  #
% 5.03/5.20  # Preprocessing time       : 0.028 s
% 5.03/5.20  # Presaturation interreduction done
% 5.03/5.20  
% 5.03/5.20  # Proof found!
% 5.03/5.20  # SZS status Theorem
% 5.03/5.20  # SZS output start CNFRefutation
% 5.03/5.20  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.03/5.20  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.03/5.20  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.03/5.20  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 5.03/5.20  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.03/5.20  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.03/5.20  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 5.03/5.20  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.03/5.20  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.03/5.20  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.03/5.20  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.03/5.20  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.03/5.20  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.03/5.20  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.03/5.20  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.03/5.20  fof(t33_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_xboole_1)).
% 5.03/5.20  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 5.03/5.20  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.03/5.20  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.03/5.20  fof(c_0_19, plain, ![X29, X30]:k2_xboole_0(X29,X30)=k5_xboole_0(X29,k4_xboole_0(X30,X29)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 5.03/5.20  fof(c_0_20, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 5.03/5.20  fof(c_0_21, plain, ![X16, X17, X18]:((r1_tarski(X16,X17)|~r1_tarski(X16,k4_xboole_0(X17,X18)))&(r1_xboole_0(X16,X18)|~r1_tarski(X16,k4_xboole_0(X17,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 5.03/5.20  fof(c_0_22, plain, ![X25]:k4_xboole_0(k1_xboole_0,X25)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 5.03/5.20  fof(c_0_23, plain, ![X19]:k2_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t1_boole])).
% 5.03/5.20  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.03/5.20  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.03/5.20  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.03/5.20  cnf(c_0_27, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.03/5.20  fof(c_0_28, plain, ![X23, X24]:r1_tarski(k4_xboole_0(X23,X24),X23), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 5.03/5.20  fof(c_0_29, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 5.03/5.20  fof(c_0_30, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 5.03/5.20  fof(c_0_31, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 5.03/5.20  cnf(c_0_32, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.03/5.20  cnf(c_0_33, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 5.03/5.20  cnf(c_0_34, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 5.03/5.20  cnf(c_0_35, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_27, c_0_25])).
% 5.03/5.20  cnf(c_0_36, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 5.03/5.20  fof(c_0_37, plain, ![X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(X40))|k3_subset_1(X40,X41)=k4_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 5.03/5.20  fof(c_0_38, plain, ![X26, X27, X28]:(~r1_tarski(X26,X27)|r1_xboole_0(X26,k4_xboole_0(X28,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 5.03/5.20  fof(c_0_39, plain, ![X31, X32, X33, X34, X35, X36]:(((~r2_hidden(X33,X32)|r1_tarski(X33,X31)|X32!=k1_zfmisc_1(X31))&(~r1_tarski(X34,X31)|r2_hidden(X34,X32)|X32!=k1_zfmisc_1(X31)))&((~r2_hidden(esk3_2(X35,X36),X36)|~r1_tarski(esk3_2(X35,X36),X35)|X36=k1_zfmisc_1(X35))&(r2_hidden(esk3_2(X35,X36),X36)|r1_tarski(esk3_2(X35,X36),X35)|X36=k1_zfmisc_1(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 5.03/5.20  fof(c_0_40, plain, ![X38, X39]:(((~m1_subset_1(X39,X38)|r2_hidden(X39,X38)|v1_xboole_0(X38))&(~r2_hidden(X39,X38)|m1_subset_1(X39,X38)|v1_xboole_0(X38)))&((~m1_subset_1(X39,X38)|v1_xboole_0(X39)|~v1_xboole_0(X38))&(~v1_xboole_0(X39)|m1_subset_1(X39,X38)|~v1_xboole_0(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 5.03/5.20  fof(c_0_41, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))&((~r1_tarski(esk5_0,esk6_0)|~r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)))&(r1_tarski(esk5_0,esk6_0)|r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 5.03/5.20  fof(c_0_42, plain, ![X44]:~v1_xboole_0(k1_zfmisc_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 5.03/5.20  cnf(c_0_43, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 5.03/5.20  cnf(c_0_44, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 5.03/5.20  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 5.03/5.20  fof(c_0_46, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 5.03/5.20  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 5.03/5.20  cnf(c_0_48, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_36, c_0_25])).
% 5.03/5.20  cnf(c_0_49, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 5.03/5.20  cnf(c_0_50, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 5.03/5.20  cnf(c_0_51, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 5.03/5.20  cnf(c_0_52, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.03/5.20  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.03/5.20  cnf(c_0_54, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 5.03/5.20  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 5.03/5.20  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_45, c_0_35])).
% 5.03/5.20  cnf(c_0_57, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 5.03/5.20  cnf(c_0_58, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_35])).
% 5.03/5.20  cnf(c_0_59, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_49, c_0_25])).
% 5.03/5.20  fof(c_0_60, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|r1_tarski(k4_xboole_0(X20,X22),k4_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_xboole_1])])).
% 5.03/5.20  cnf(c_0_61, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_50, c_0_25])).
% 5.03/5.20  cnf(c_0_62, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_51])).
% 5.03/5.20  cnf(c_0_63, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 5.03/5.20  cnf(c_0_64, plain, (r1_tarski(X1,X1)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_55]), c_0_56])).
% 5.03/5.20  cnf(c_0_65, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 5.03/5.20  cnf(c_0_66, plain, (k3_subset_1(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_55]), c_0_56])).
% 5.03/5.20  cnf(c_0_67, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 5.03/5.20  cnf(c_0_68, plain, (r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 5.03/5.20  cnf(c_0_69, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_55]), c_0_56])).
% 5.03/5.20  cnf(c_0_70, negated_conjecture, (r1_tarski(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 5.03/5.20  cnf(c_0_71, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 5.03/5.20  cnf(c_0_72, plain, (k3_subset_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=X1|~m1_subset_1(k5_xboole_0(X2,k3_xboole_0(X2,X3)),k1_zfmisc_1(X1))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_66, c_0_61])).
% 5.03/5.20  cnf(c_0_73, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.03/5.20  cnf(c_0_74, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_67])).
% 5.03/5.20  cnf(c_0_75, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X3)),k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_25]), c_0_25])).
% 5.03/5.20  cnf(c_0_76, negated_conjecture, (r1_xboole_0(esk6_0,X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 5.03/5.20  cnf(c_0_77, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_34, c_0_71])).
% 5.03/5.20  cnf(c_0_78, plain, (k3_subset_1(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_55]), c_0_56]), c_0_56])).
% 5.03/5.20  cnf(c_0_79, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_54])).
% 5.03/5.20  cnf(c_0_80, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X1,X4)|~r1_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X2)))), inference(spm,[status(thm)],[c_0_69, c_0_75])).
% 5.03/5.20  cnf(c_0_81, negated_conjecture, (r1_xboole_0(esk6_0,k5_xboole_0(X1,k3_xboole_0(X1,esk4_0)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 5.03/5.20  cnf(c_0_82, plain, (k3_subset_1(X1,X2)=X1|~r1_tarski(X1,X3)|~r1_tarski(X2,X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 5.03/5.20  cnf(c_0_83, negated_conjecture, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,esk4_0)),esk6_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 5.03/5.20  fof(c_0_84, plain, ![X42, X43]:m1_subset_1(k6_subset_1(X42,X43),k1_zfmisc_1(X42)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 5.03/5.20  fof(c_0_85, plain, ![X47, X48]:k6_subset_1(X47,X48)=k4_xboole_0(X47,X48), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 5.03/5.20  fof(c_0_86, plain, ![X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(X45))|k3_subset_1(X45,k3_subset_1(X45,X46))=X46), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 5.03/5.20  cnf(c_0_87, plain, (k3_subset_1(X1,X2)=X1|~r1_tarski(X2,X1)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_82, c_0_71])).
% 5.03/5.20  cnf(c_0_88, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk4_0)),esk6_0)), inference(spm,[status(thm)],[c_0_83, c_0_70])).
% 5.03/5.20  cnf(c_0_89, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 5.03/5.20  cnf(c_0_90, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 5.03/5.20  cnf(c_0_91, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 5.03/5.20  cnf(c_0_92, negated_conjecture, (k3_subset_1(esk6_0,k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk4_0)))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_48])])).
% 5.03/5.20  cnf(c_0_93, plain, (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90]), c_0_25])).
% 5.03/5.20  cnf(c_0_94, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X3,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_55]), c_0_56])).
% 5.03/5.20  cnf(c_0_95, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_57, c_0_77])).
% 5.03/5.20  cnf(c_0_96, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk4_0))=k3_subset_1(esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])])).
% 5.03/5.20  cnf(c_0_97, negated_conjecture, (r1_xboole_0(esk6_0,X1)|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_94, c_0_70])).
% 5.03/5.20  cnf(c_0_98, negated_conjecture, (r1_xboole_0(esk4_0,k3_subset_1(esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 5.03/5.20  cnf(c_0_99, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.03/5.20  cnf(c_0_100, negated_conjecture, (r1_xboole_0(X1,esk6_0)|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_97])).
% 5.03/5.20  cnf(c_0_101, negated_conjecture, (k3_subset_1(esk4_0,k3_subset_1(esk6_0,esk6_0))=esk4_0|~m1_subset_1(k3_subset_1(esk6_0,esk6_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_66, c_0_98])).
% 5.03/5.20  cnf(c_0_102, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_99, c_0_25])).
% 5.03/5.20  cnf(c_0_103, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_94, c_0_48])).
% 5.03/5.20  cnf(c_0_104, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_subset_1(X3,X2))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_75, c_0_59])).
% 5.03/5.20  cnf(c_0_105, negated_conjecture, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),esk6_0)|~r1_tarski(esk4_0,X2)), inference(spm,[status(thm)],[c_0_100, c_0_61])).
% 5.03/5.20  cnf(c_0_106, negated_conjecture, (k3_subset_1(esk6_0,esk6_0)=k3_subset_1(esk4_0,esk4_0)|~m1_subset_1(k3_subset_1(esk6_0,esk6_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_91, c_0_101])).
% 5.03/5.20  cnf(c_0_107, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_102, c_0_75])).
% 5.03/5.20  cnf(c_0_108, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.03/5.20  cnf(c_0_109, negated_conjecture, (r1_tarski(esk5_0,esk6_0)|r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.03/5.20  cnf(c_0_110, plain, (r1_xboole_0(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_103, c_0_59])).
% 5.03/5.20  cnf(c_0_111, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_55]), c_0_56])).
% 5.03/5.20  cnf(c_0_112, negated_conjecture, (r1_xboole_0(X1,esk6_0)|~r1_tarski(esk4_0,X2)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_55]), c_0_56])).
% 5.03/5.20  cnf(c_0_113, negated_conjecture, (k3_subset_1(esk6_0,esk6_0)=k3_subset_1(esk4_0,esk4_0)|~r1_tarski(k3_subset_1(esk6_0,esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_106, c_0_79])).
% 5.03/5.20  cnf(c_0_114, negated_conjecture, (r1_tarski(k3_subset_1(esk6_0,esk6_0),X1)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_107, c_0_96])).
% 5.03/5.20  cnf(c_0_115, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(spm,[status(thm)],[c_0_102, c_0_59])).
% 5.03/5.20  cnf(c_0_116, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_93, c_0_59])).
% 5.03/5.20  cnf(c_0_117, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_108]), c_0_54])).
% 5.03/5.20  cnf(c_0_118, negated_conjecture, (r1_tarski(esk5_0,esk6_0)|r1_xboole_0(k3_subset_1(esk4_0,esk6_0),X1)|~r1_xboole_0(k3_subset_1(esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_94, c_0_109])).
% 5.03/5.20  cnf(c_0_119, plain, (r1_xboole_0(k3_subset_1(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_77, c_0_59])).
% 5.03/5.20  cnf(c_0_120, plain, (r1_xboole_0(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_57, c_0_110])).
% 5.03/5.20  cnf(c_0_121, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk4_0,esk6_0))|~r1_tarski(X1,esk4_0)|~r1_xboole_0(X1,esk6_0)), inference(spm,[status(thm)],[c_0_111, c_0_53])).
% 5.03/5.20  cnf(c_0_122, negated_conjecture, (r1_xboole_0(X1,esk6_0)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_112, c_0_71])).
% 5.03/5.20  cnf(c_0_123, negated_conjecture, (r1_xboole_0(k3_subset_1(esk6_0,esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_77, c_0_96])).
% 5.03/5.20  cnf(c_0_124, negated_conjecture, (k3_subset_1(esk6_0,esk6_0)=k3_subset_1(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_70])])).
% 5.03/5.20  cnf(c_0_125, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_91]), c_0_116])).
% 5.03/5.20  cnf(c_0_126, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_111, c_0_79])).
% 5.03/5.20  cnf(c_0_127, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_117])).
% 5.03/5.20  cnf(c_0_128, negated_conjecture, (r1_tarski(esk5_0,esk6_0)|r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_108])])).
% 5.03/5.20  cnf(c_0_129, negated_conjecture, (r1_xboole_0(X1,k3_subset_1(esk4_0,esk6_0))|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_120, c_0_53])).
% 5.03/5.20  cnf(c_0_130, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk4_0,esk6_0))|~r1_tarski(X1,esk4_0)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 5.03/5.20  cnf(c_0_131, negated_conjecture, (r1_xboole_0(k3_subset_1(esk4_0,esk4_0),esk4_0)), inference(rw,[status(thm)],[c_0_123, c_0_124])).
% 5.03/5.20  cnf(c_0_132, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_125, c_0_53])).
% 5.03/5.20  cnf(c_0_133, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk4_0),X1)|~r1_tarski(esk6_0,X1)), inference(rw,[status(thm)],[c_0_114, c_0_124])).
% 5.03/5.20  cnf(c_0_134, negated_conjecture, (r1_tarski(esk5_0,k3_subset_1(esk4_0,X1))|~r1_tarski(X1,esk4_0)|~r1_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 5.03/5.20  cnf(c_0_135, negated_conjecture, (r1_tarski(esk5_0,esk6_0)|r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_57, c_0_128])).
% 5.03/5.20  cnf(c_0_136, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk6_0),esk4_0)|r1_tarski(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_109]), c_0_108])])).
% 5.03/5.20  cnf(c_0_137, negated_conjecture, (r1_xboole_0(k3_subset_1(esk6_0,esk6_0),k3_subset_1(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_129, c_0_98])).
% 5.03/5.20  cnf(c_0_138, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk4_0),k3_subset_1(esk4_0,esk6_0))|~r1_tarski(k3_subset_1(esk4_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 5.03/5.20  cnf(c_0_139, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_71])])).
% 5.03/5.20  cnf(c_0_140, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_57, c_0_61])).
% 5.03/5.20  cnf(c_0_141, negated_conjecture, (r1_tarski(esk5_0,k3_subset_1(esk4_0,k3_subset_1(esk4_0,esk6_0)))|r1_tarski(esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_136])).
% 5.03/5.20  cnf(c_0_142, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X2))), inference(spm,[status(thm)],[c_0_34, c_0_59])).
% 5.03/5.20  cnf(c_0_143, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_59])).
% 5.03/5.20  cnf(c_0_144, negated_conjecture, (r1_xboole_0(k3_subset_1(esk4_0,esk4_0),k3_subset_1(esk4_0,esk6_0))), inference(rw,[status(thm)],[c_0_137, c_0_124])).
% 5.03/5.20  cnf(c_0_145, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk4_0),k3_subset_1(esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_138, c_0_139])])).
% 5.03/5.20  cnf(c_0_146, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X2,X3)|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_55]), c_0_56])).
% 5.03/5.20  cnf(c_0_147, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_91]), c_0_53])])).
% 5.03/5.20  cnf(c_0_148, plain, (r1_xboole_0(k3_subset_1(k3_subset_1(X1,X2),X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_142, c_0_143])).
% 5.03/5.20  cnf(c_0_149, negated_conjecture, (k3_subset_1(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk4_0))=k3_subset_1(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_144]), c_0_145])])).
% 5.03/5.20  cnf(c_0_150, plain, (r1_tarski(k3_subset_1(k3_subset_1(X1,X2),X3),X1)|~m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_115, c_0_143])).
% 5.03/5.20  cnf(c_0_151, negated_conjecture, (r1_xboole_0(X1,esk5_0)|~r1_xboole_0(X1,esk6_0)), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 5.03/5.20  cnf(c_0_152, negated_conjecture, (r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk6_0)|~m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(k3_subset_1(esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_53])])).
% 5.03/5.20  cnf(c_0_153, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk6_0),esk4_0)|~m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(k3_subset_1(esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_149]), c_0_53])])).
% 5.03/5.20  cnf(c_0_154, negated_conjecture, (~r1_tarski(esk5_0,esk6_0)|~r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.03/5.20  cnf(c_0_155, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk4_0,esk5_0))|~r1_tarski(X1,esk4_0)|~r1_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_111, c_0_108])).
% 5.03/5.20  cnf(c_0_156, negated_conjecture, (r1_xboole_0(k3_subset_1(esk4_0,esk6_0),esk5_0)|~m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(k3_subset_1(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_151, c_0_152])).
% 5.03/5.20  cnf(c_0_157, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk6_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_79]), c_0_145])])).
% 5.03/5.20  cnf(c_0_158, negated_conjecture, (~r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154, c_0_147])])).
% 5.03/5.20  cnf(c_0_159, negated_conjecture, (~m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(k3_subset_1(esk4_0,esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_156]), c_0_157])]), c_0_158])).
% 5.03/5.20  cnf(c_0_160, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_79]), c_0_145])]), ['proof']).
% 5.03/5.20  # SZS output end CNFRefutation
% 5.03/5.20  # Proof object total steps             : 161
% 5.03/5.20  # Proof object clause steps            : 122
% 5.03/5.20  # Proof object formula steps           : 39
% 5.03/5.20  # Proof object conjectures             : 57
% 5.03/5.20  # Proof object clause conjectures      : 54
% 5.03/5.20  # Proof object formula conjectures     : 3
% 5.03/5.20  # Proof object initial clauses used    : 25
% 5.03/5.20  # Proof object initial formulas used   : 19
% 5.03/5.20  # Proof object generating inferences   : 79
% 5.03/5.20  # Proof object simplifying inferences  : 64
% 5.03/5.20  # Training examples: 0 positive, 0 negative
% 5.03/5.20  # Parsed axioms                        : 19
% 5.03/5.20  # Removed by relevancy pruning/SinE    : 0
% 5.03/5.20  # Initial clauses                      : 30
% 5.03/5.20  # Removed in clause preprocessing      : 3
% 5.03/5.20  # Initial clauses in saturation        : 27
% 5.03/5.20  # Processed clauses                    : 31655
% 5.03/5.20  # ...of these trivial                  : 584
% 5.03/5.20  # ...subsumed                          : 26604
% 5.03/5.20  # ...remaining for further processing  : 4467
% 5.03/5.20  # Other redundant clauses eliminated   : 2
% 5.03/5.20  # Clauses deleted for lack of memory   : 0
% 5.03/5.20  # Backward-subsumed                    : 659
% 5.03/5.20  # Backward-rewritten                   : 471
% 5.03/5.20  # Generated clauses                    : 601868
% 5.03/5.20  # ...of the previous two non-trivial   : 546799
% 5.03/5.20  # Contextual simplify-reflections      : 157
% 5.03/5.20  # Paramodulations                      : 601740
% 5.03/5.20  # Factorizations                       : 126
% 5.03/5.20  # Equation resolutions                 : 2
% 5.03/5.20  # Propositional unsat checks           : 0
% 5.03/5.20  #    Propositional check models        : 0
% 5.03/5.20  #    Propositional check unsatisfiable : 0
% 5.03/5.20  #    Propositional clauses             : 0
% 5.03/5.20  #    Propositional clauses after purity: 0
% 5.03/5.20  #    Propositional unsat core size     : 0
% 5.03/5.20  #    Propositional preprocessing time  : 0.000
% 5.03/5.20  #    Propositional encoding time       : 0.000
% 5.03/5.20  #    Propositional solver time         : 0.000
% 5.03/5.20  #    Success case prop preproc time    : 0.000
% 5.03/5.20  #    Success case prop encoding time   : 0.000
% 5.03/5.20  #    Success case prop solver time     : 0.000
% 5.03/5.20  # Current number of processed clauses  : 3308
% 5.03/5.20  #    Positive orientable unit clauses  : 203
% 5.03/5.20  #    Positive unorientable unit clauses: 0
% 5.03/5.20  #    Negative unit clauses             : 37
% 5.03/5.20  #    Non-unit-clauses                  : 3068
% 5.03/5.20  # Current number of unprocessed clauses: 510712
% 5.03/5.20  # ...number of literals in the above   : 1964597
% 5.03/5.20  # Current number of archived formulas  : 0
% 5.03/5.20  # Current number of archived clauses   : 1160
% 5.03/5.20  # Clause-clause subsumption calls (NU) : 1470351
% 5.03/5.20  # Rec. Clause-clause subsumption calls : 835192
% 5.03/5.20  # Non-unit clause-clause subsumptions  : 12170
% 5.03/5.20  # Unit Clause-clause subsumption calls : 19158
% 5.03/5.20  # Rewrite failures with RHS unbound    : 0
% 5.03/5.20  # BW rewrite match attempts            : 2609
% 5.03/5.20  # BW rewrite match successes           : 36
% 5.03/5.20  # Condensation attempts                : 0
% 5.03/5.20  # Condensation successes               : 0
% 5.03/5.20  # Termbank termtop insertions          : 12961563
% 5.03/5.22  
% 5.03/5.22  # -------------------------------------------------
% 5.03/5.22  # User time                : 4.708 s
% 5.03/5.22  # System time              : 0.172 s
% 5.03/5.22  # Total time               : 4.880 s
% 5.03/5.22  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
