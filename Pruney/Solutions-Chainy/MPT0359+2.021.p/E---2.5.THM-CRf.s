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
% DateTime   : Thu Dec  3 10:46:02 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 240 expanded)
%              Number of clauses        :   38 ( 105 expanded)
%              Number of leaves         :   17 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 514 expanded)
%              Number of equality atoms :   58 ( 213 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t39_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(k3_subset_1(X1,X2),X2)
      <=> X2 = k2_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

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

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_17,plain,(
    ! [X17,X18] : r1_xboole_0(k4_xboole_0(X17,X18),X18) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_18,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | k3_subset_1(X33,X34) = k4_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_20,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(k3_subset_1(X1,X2),X2)
        <=> X2 = k2_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t39_subset_1])).

fof(c_0_24,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X16)
      | ~ r1_tarski(X16,X15)
      | ~ r1_xboole_0(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)
      | esk3_0 != k2_subset_1(esk2_0) )
    & ( r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)
      | esk3_0 = k2_subset_1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_28,plain,(
    ! [X32] : k2_subset_1(X32) = X32 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_29,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X25,X24)
        | r1_tarski(X25,X23)
        | X24 != k1_zfmisc_1(X23) )
      & ( ~ r1_tarski(X26,X23)
        | r2_hidden(X26,X24)
        | X24 != k1_zfmisc_1(X23) )
      & ( ~ r2_hidden(esk1_2(X27,X28),X28)
        | ~ r1_tarski(esk1_2(X27,X28),X27)
        | X28 = k1_zfmisc_1(X27) )
      & ( r2_hidden(esk1_2(X27,X28),X28)
        | r1_tarski(esk1_2(X27,X28),X27)
        | X28 = k1_zfmisc_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_30,plain,(
    ! [X30,X31] :
      ( ( ~ m1_subset_1(X31,X30)
        | r2_hidden(X31,X30)
        | v1_xboole_0(X30) )
      & ( ~ r2_hidden(X31,X30)
        | m1_subset_1(X31,X30)
        | v1_xboole_0(X30) )
      & ( ~ m1_subset_1(X31,X30)
        | v1_xboole_0(X31)
        | ~ v1_xboole_0(X30) )
      & ( ~ v1_xboole_0(X31)
        | m1_subset_1(X31,X30)
        | ~ v1_xboole_0(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_31,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k3_xboole_0(X11,X12) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_32,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_xboole_0(k3_subset_1(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)
    | esk3_0 = k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X35] : ~ v1_xboole_0(k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_40,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_41,plain,(
    ! [X19,X20,X21] : k5_xboole_0(k5_xboole_0(X19,X20),X21) = k5_xboole_0(X19,k5_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 = esk2_0
    | r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | v1_xboole_0(X3)
    | X3 != k1_zfmisc_1(X2)
    | ~ m1_subset_1(X1,X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_52,plain,(
    ! [X22] : k5_xboole_0(X22,X22) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_53,plain,(
    ! [X14] : k5_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( esk2_0 = esk3_0
    | v1_xboole_0(k3_subset_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | k1_zfmisc_1(esk2_0) != k1_zfmisc_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_47]),c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)
    | esk3_0 != k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( k3_subset_1(X1,X2) = k5_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k1_xboole_0
    | esk2_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( esk3_0 != esk2_0
    | ~ r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_36])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk2_0) = k1_xboole_0
    | esk2_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_50]),c_0_47]),c_0_64])])).

fof(c_0_68,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_69,negated_conjecture,
    ( esk2_0 != esk3_0
    | ~ r1_tarski(k5_xboole_0(esk3_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_62]),c_0_47]),c_0_64])]),c_0_50])).

cnf(c_0_70,negated_conjecture,
    ( esk2_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_61])])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_70]),c_0_60]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:49:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.12/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.022 s
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.12/0.36  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.36  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.12/0.36  fof(t39_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 0.12/0.36  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.12/0.36  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.12/0.36  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.12/0.36  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.12/0.36  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.36  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.12/0.36  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.12/0.36  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.12/0.36  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.12/0.36  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.12/0.36  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.12/0.36  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.12/0.36  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.36  fof(c_0_17, plain, ![X17, X18]:r1_xboole_0(k4_xboole_0(X17,X18),X18), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.12/0.36  fof(c_0_18, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.36  fof(c_0_19, plain, ![X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|k3_subset_1(X33,X34)=k4_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.12/0.36  cnf(c_0_20, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_22, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.36  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1)))), inference(assume_negation,[status(cth)],[t39_subset_1])).
% 0.12/0.36  fof(c_0_24, plain, ![X15, X16]:(v1_xboole_0(X16)|(~r1_tarski(X16,X15)|~r1_xboole_0(X16,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.12/0.36  cnf(c_0_25, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.36  cnf(c_0_26, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.12/0.36  fof(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)|esk3_0!=k2_subset_1(esk2_0))&(r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)|esk3_0=k2_subset_1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.12/0.36  fof(c_0_28, plain, ![X32]:k2_subset_1(X32)=X32, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.12/0.36  fof(c_0_29, plain, ![X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X25,X24)|r1_tarski(X25,X23)|X24!=k1_zfmisc_1(X23))&(~r1_tarski(X26,X23)|r2_hidden(X26,X24)|X24!=k1_zfmisc_1(X23)))&((~r2_hidden(esk1_2(X27,X28),X28)|~r1_tarski(esk1_2(X27,X28),X27)|X28=k1_zfmisc_1(X27))&(r2_hidden(esk1_2(X27,X28),X28)|r1_tarski(esk1_2(X27,X28),X27)|X28=k1_zfmisc_1(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.12/0.36  fof(c_0_30, plain, ![X30, X31]:(((~m1_subset_1(X31,X30)|r2_hidden(X31,X30)|v1_xboole_0(X30))&(~r2_hidden(X31,X30)|m1_subset_1(X31,X30)|v1_xboole_0(X30)))&((~m1_subset_1(X31,X30)|v1_xboole_0(X31)|~v1_xboole_0(X30))&(~v1_xboole_0(X31)|m1_subset_1(X31,X30)|~v1_xboole_0(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.12/0.36  fof(c_0_31, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k3_xboole_0(X11,X12)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.12/0.36  fof(c_0_32, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.12/0.36  cnf(c_0_33, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.36  cnf(c_0_34, plain, (r1_xboole_0(k3_subset_1(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.36  cnf(c_0_35, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)|esk3_0=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_36, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.36  cnf(c_0_37, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.36  cnf(c_0_38, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.36  fof(c_0_39, plain, ![X35]:~v1_xboole_0(k1_zfmisc_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.12/0.36  fof(c_0_40, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.12/0.36  fof(c_0_41, plain, ![X19, X20, X21]:k5_xboole_0(k5_xboole_0(X19,X20),X21)=k5_xboole_0(X19,k5_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.12/0.36  cnf(c_0_42, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.36  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.36  fof(c_0_44, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.12/0.36  cnf(c_0_45, plain, (v1_xboole_0(k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k3_subset_1(X1,X2),X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.36  cnf(c_0_46, negated_conjecture, (esk3_0=esk2_0|r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.36  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_48, plain, (r1_tarski(X1,X2)|v1_xboole_0(X3)|X3!=k1_zfmisc_1(X2)|~m1_subset_1(X1,X3)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.36  cnf(c_0_49, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.36  cnf(c_0_50, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.36  cnf(c_0_51, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.36  fof(c_0_52, plain, ![X22]:k5_xboole_0(X22,X22)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.12/0.36  fof(c_0_53, plain, ![X14]:k5_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.12/0.36  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.36  cnf(c_0_55, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.36  cnf(c_0_56, negated_conjecture, (esk2_0=esk3_0|v1_xboole_0(k3_subset_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.12/0.36  cnf(c_0_57, negated_conjecture, (r1_tarski(esk3_0,X1)|k1_zfmisc_1(esk2_0)!=k1_zfmisc_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_47]), c_0_49])).
% 0.12/0.36  cnf(c_0_58, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)|esk3_0!=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_59, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.12/0.36  cnf(c_0_60, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.12/0.36  cnf(c_0_61, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.12/0.36  cnf(c_0_62, plain, (k3_subset_1(X1,X2)=k5_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_54])).
% 0.12/0.36  cnf(c_0_63, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k1_xboole_0|esk2_0=esk3_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.12/0.36  cnf(c_0_64, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(er,[status(thm)],[c_0_57])).
% 0.12/0.36  cnf(c_0_65, negated_conjecture, (esk3_0!=esk2_0|~r1_tarski(k3_subset_1(esk2_0,esk3_0),esk3_0)), inference(rw,[status(thm)],[c_0_58, c_0_36])).
% 0.12/0.36  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.12/0.36  cnf(c_0_67, negated_conjecture, (k5_xboole_0(esk3_0,esk2_0)=k1_xboole_0|esk2_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_50]), c_0_47]), c_0_64])])).
% 0.12/0.36  fof(c_0_68, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.36  cnf(c_0_69, negated_conjecture, (esk2_0!=esk3_0|~r1_tarski(k5_xboole_0(esk3_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_62]), c_0_47]), c_0_64])]), c_0_50])).
% 0.12/0.36  cnf(c_0_70, negated_conjecture, (esk2_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_61])])).
% 0.12/0.36  cnf(c_0_71, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.12/0.36  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_70]), c_0_60]), c_0_71])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 73
% 0.12/0.36  # Proof object clause steps            : 38
% 0.12/0.36  # Proof object formula steps           : 35
% 0.12/0.36  # Proof object conjectures             : 16
% 0.12/0.36  # Proof object clause conjectures      : 13
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 19
% 0.12/0.36  # Proof object initial formulas used   : 17
% 0.12/0.36  # Proof object generating inferences   : 14
% 0.12/0.36  # Proof object simplifying inferences  : 23
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 17
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 25
% 0.12/0.36  # Removed in clause preprocessing      : 2
% 0.12/0.36  # Initial clauses in saturation        : 23
% 0.12/0.36  # Processed clauses                    : 98
% 0.12/0.36  # ...of these trivial                  : 2
% 0.12/0.36  # ...subsumed                          : 24
% 0.12/0.36  # ...remaining for further processing  : 72
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 2
% 0.12/0.36  # Backward-rewritten                   : 22
% 0.12/0.36  # Generated clauses                    : 284
% 0.12/0.36  # ...of the previous two non-trivial   : 230
% 0.12/0.36  # Contextual simplify-reflections      : 1
% 0.12/0.36  # Paramodulations                      : 279
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 5
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 48
% 0.12/0.36  #    Positive orientable unit clauses  : 15
% 0.12/0.36  #    Positive unorientable unit clauses: 3
% 0.12/0.36  #    Negative unit clauses             : 1
% 0.12/0.36  #    Non-unit-clauses                  : 29
% 0.12/0.36  # Current number of unprocessed clauses: 148
% 0.12/0.36  # ...number of literals in the above   : 291
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 26
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 170
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 134
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 24
% 0.12/0.36  # Unit Clause-clause subsumption calls : 26
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 17
% 0.12/0.36  # BW rewrite match successes           : 12
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 3945
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.026 s
% 0.12/0.36  # System time              : 0.005 s
% 0.12/0.36  # Total time               : 0.031 s
% 0.12/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
