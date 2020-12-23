%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:58 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 617 expanded)
%              Number of clauses        :   60 ( 269 expanded)
%              Number of leaves         :   10 ( 157 expanded)
%              Depth                    :    9
%              Number of atoms          :  191 (1537 expanded)
%              Number of equality atoms :   73 ( 676 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t25_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( k2_struct_0(X1) = k4_subset_1(u1_struct_0(X1),X2,X3)
                  & r1_xboole_0(X2,X3) )
               => X3 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_pre_topc)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(c_0_10,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | ~ m1_subset_1(X18,k1_zfmisc_1(X16))
      | k4_subset_1(X16,X17,X18) = k2_xboole_0(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_11,plain,(
    ! [X14,X15] : k3_tarski(k2_tarski(X14,X15)) = k2_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( k2_struct_0(X1) = k4_subset_1(u1_struct_0(X1),X2,X3)
                    & r1_xboole_0(X2,X3) )
                 => X3 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_pre_topc])).

cnf(c_0_13,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_16,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_17,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & k2_struct_0(esk1_0) = k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)
    & r1_xboole_0(esk2_0,esk3_0)
    & esk3_0 != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_18,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14]),
    [final]).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k2_struct_0(esk1_0) = k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_22,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_18]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

fof(c_0_25,plain,(
    ! [X12,X13] :
      ( ( ~ r1_xboole_0(X12,X13)
        | k4_xboole_0(X12,X13) = X12 )
      & ( k4_xboole_0(X12,X13) != X12
        | r1_xboole_0(X12,X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_14]),
    [final]).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_14]),c_0_14]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( k4_subset_1(X1,esk2_0,esk3_0) = k2_struct_0(esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])]),
    [final]).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

fof(c_0_30,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_31,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_32,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_34,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27]),
    [final]).

fof(c_0_35,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | k7_subset_1(X19,X20,X21) = k4_xboole_0(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_36,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,esk3_0)) = k2_struct_0(esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_28])).

cnf(c_0_37,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k4_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_29]),
    [final]).

cnf(c_0_38,plain,
    ( k4_xboole_0(k4_subset_1(X1,X2,X3),X3) = k4_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_18]),
    [final]).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_41,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_42,plain,
    ( r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | k3_tarski(k2_tarski(X1,X2)) != k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34]),
    [final]).

cnf(c_0_43,plain,
    ( r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | k3_tarski(k2_tarski(X1,X2)) != k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( esk3_0 != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_45,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,esk3_0)) = k2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_24])]),
    [final]).

cnf(c_0_47,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k4_xboole_0(X2,X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(k2_struct_0(esk1_0),esk3_0) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_21]),c_0_23]),c_0_24])]),
    [final]).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40]),
    [final]).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_51,plain,
    ( k4_subset_1(X1,X2,X3) = k3_tarski(k2_tarski(X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_18]),
    [final]).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | k3_tarski(k2_tarski(X1,X2)) != k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42]),
    [final]).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,k3_tarski(k2_tarski(X2,X1)))
    | k3_tarski(k2_tarski(X2,X1)) != k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_43]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(k2_struct_0(esk1_0),esk2_0) != esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(k2_struct_0(esk1_0),esk2_0) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_46]),
    [final]).

cnf(c_0_56,plain,
    ( k4_subset_1(X1,X2,X3) = k4_xboole_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_18]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | k2_struct_0(esk1_0) != k4_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_48]),
    [final]).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_50]),
    [final]).

cnf(c_0_62,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_51]),
    [final]).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,k4_subset_1(X2,X1,X3))
    | k4_subset_1(X2,X1,X3) != k4_xboole_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_18]),
    [final]).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,k4_subset_1(X2,X3,X1))
    | k4_subset_1(X2,X3,X1) != k4_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_18]),
    [final]).

cnf(c_0_65,plain,
    ( r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | k4_subset_1(X1,X2,X3) != k4_xboole_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_18]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( k4_subset_1(X1,esk3_0,esk2_0) = k2_struct_0(esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_46]),
    [final]).

cnf(c_0_67,plain,
    ( k4_xboole_0(k4_subset_1(X1,X2,X3),X2) = k4_xboole_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_18]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) != esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | k2_struct_0(esk1_0) != k4_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_46]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | k2_struct_0(esk1_0) != k4_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_46]),
    [final]).

cnf(c_0_71,plain,
    ( r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | k4_subset_1(X1,X2,X3) != k4_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_18]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( k2_struct_0(esk1_0) = k4_xboole_0(esk3_0,esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_21]),c_0_23]),c_0_24])]),
    [final]).

cnf(c_0_73,plain,
    ( k4_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_18]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | k2_struct_0(esk1_0) != k4_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_57]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( k2_struct_0(esk1_0) = k4_xboole_0(esk2_0,esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_48]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_24]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk3_0
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_23]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_59]),
    [final]).

cnf(c_0_79,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:56:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # No proof found!
% 0.12/0.37  # SZS status CounterSatisfiable
% 0.12/0.37  # SZS output start Saturation
% 0.12/0.37  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.12/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.37  fof(t25_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_pre_topc)).
% 0.12/0.37  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.12/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.12/0.37  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.12/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.12/0.37  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.12/0.37  fof(c_0_10, plain, ![X16, X17, X18]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|~m1_subset_1(X18,k1_zfmisc_1(X16))|k4_subset_1(X16,X17,X18)=k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.12/0.37  fof(c_0_11, plain, ![X14, X15]:k3_tarski(k2_tarski(X14,X15))=k2_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.37  fof(c_0_12, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t25_pre_topc])).
% 0.12/0.37  cnf(c_0_13, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  fof(c_0_15, plain, ![X10, X11]:k4_xboole_0(k2_xboole_0(X10,X11),X11)=k4_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.12/0.37  fof(c_0_16, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.12/0.37  fof(c_0_17, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((k2_struct_0(esk1_0)=k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)&r1_xboole_0(esk2_0,esk3_0))&esk3_0!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.12/0.37  cnf(c_0_18, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.12/0.37  cnf(c_0_19, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (k2_struct_0(esk1_0)=k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.12/0.37  cnf(c_0_22, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_18, c_0_18]), ['final']).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.12/0.37  fof(c_0_25, plain, ![X12, X13]:((~r1_xboole_0(X12,X13)|k4_xboole_0(X12,X13)=X12)&(k4_xboole_0(X12,X13)!=X12|r1_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.12/0.37  cnf(c_0_26, plain, (k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_14]), ['final']).
% 0.12/0.37  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k3_tarski(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_14]), c_0_14]), ['final']).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (k4_subset_1(X1,esk2_0,esk3_0)=k2_struct_0(esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])]), ['final']).
% 0.12/0.37  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.12/0.37  fof(c_0_30, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.37  fof(c_0_31, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.37  fof(c_0_32, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.12/0.37  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.12/0.37  cnf(c_0_34, plain, (k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27]), ['final']).
% 0.12/0.37  fof(c_0_35, plain, ![X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|k7_subset_1(X19,X20,X21)=k4_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,esk3_0))=k2_struct_0(esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_18, c_0_28])).
% 0.12/0.37  cnf(c_0_37, plain, (k3_tarski(k2_tarski(X1,X2))=k4_xboole_0(X1,X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_26, c_0_29]), ['final']).
% 0.12/0.37  cnf(c_0_38, plain, (k4_xboole_0(k4_subset_1(X1,X2,X3),X3)=k4_xboole_0(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_18]), ['final']).
% 0.12/0.37  cnf(c_0_39, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.12/0.37  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.12/0.37  cnf(c_0_41, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.12/0.37  cnf(c_0_42, plain, (r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|k3_tarski(k2_tarski(X1,X2))!=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34]), ['final']).
% 0.12/0.37  cnf(c_0_43, plain, (r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|k3_tarski(k2_tarski(X1,X2))!=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_26]), ['final']).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (esk3_0!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.12/0.37  cnf(c_0_45, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,esk3_0))=k2_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_23]), c_0_24])]), ['final']).
% 0.12/0.37  cnf(c_0_47, plain, (k3_tarski(k2_tarski(X1,X2))=k4_xboole_0(X2,X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_37, c_0_27]), ['final']).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (k4_xboole_0(k2_struct_0(esk1_0),esk3_0)=k4_xboole_0(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_21]), c_0_23]), c_0_24])]), ['final']).
% 0.12/0.37  cnf(c_0_49, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40]), ['final']).
% 0.12/0.37  cnf(c_0_50, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  cnf(c_0_51, plain, (k4_subset_1(X1,X2,X3)=k3_tarski(k2_tarski(X3,X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_18]), ['final']).
% 0.12/0.37  cnf(c_0_52, plain, (r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|k3_tarski(k2_tarski(X1,X2))!=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42]), ['final']).
% 0.12/0.37  cnf(c_0_53, plain, (r1_xboole_0(X1,k3_tarski(k2_tarski(X2,X1)))|k3_tarski(k2_tarski(X2,X1))!=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_43]), ['final']).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (k4_xboole_0(k2_struct_0(esk1_0),esk2_0)!=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (k4_xboole_0(k2_struct_0(esk1_0),esk2_0)=k4_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_46]), ['final']).
% 0.12/0.37  cnf(c_0_56, plain, (k4_subset_1(X1,X2,X3)=k4_xboole_0(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)), inference(spm,[status(thm)],[c_0_47, c_0_18]), ['final']).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|k2_struct_0(esk1_0)!=k4_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_48]), ['final']).
% 0.12/0.37  cnf(c_0_58, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_49, c_0_40]), ['final']).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.12/0.37  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.12/0.37  cnf(c_0_61, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_50]), ['final']).
% 0.12/0.37  cnf(c_0_62, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_18, c_0_51]), ['final']).
% 0.12/0.37  cnf(c_0_63, plain, (r1_xboole_0(X1,k4_subset_1(X2,X1,X3))|k4_subset_1(X2,X1,X3)!=k4_xboole_0(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_52, c_0_18]), ['final']).
% 0.12/0.37  cnf(c_0_64, plain, (r1_xboole_0(X1,k4_subset_1(X2,X3,X1))|k4_subset_1(X2,X3,X1)!=k4_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_53, c_0_18]), ['final']).
% 0.12/0.37  cnf(c_0_65, plain, (r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|k4_subset_1(X1,X2,X3)!=k4_xboole_0(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_18]), ['final']).
% 0.12/0.37  cnf(c_0_66, negated_conjecture, (k4_subset_1(X1,esk3_0,esk2_0)=k2_struct_0(esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_46]), ['final']).
% 0.12/0.37  cnf(c_0_67, plain, (k4_xboole_0(k4_subset_1(X1,X2,X3),X2)=k4_xboole_0(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_18]), ['final']).
% 0.12/0.37  cnf(c_0_68, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)!=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[c_0_54, c_0_55]), ['final']).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, (r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|k2_struct_0(esk1_0)!=k4_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_46]), ['final']).
% 0.12/0.37  cnf(c_0_70, negated_conjecture, (r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|k2_struct_0(esk1_0)!=k4_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_52, c_0_46]), ['final']).
% 0.12/0.37  cnf(c_0_71, plain, (r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|k4_subset_1(X1,X2,X3)!=k4_xboole_0(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_18]), ['final']).
% 0.12/0.37  cnf(c_0_72, negated_conjecture, (k2_struct_0(esk1_0)=k4_xboole_0(esk3_0,esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_21]), c_0_23]), c_0_24])]), ['final']).
% 0.12/0.37  cnf(c_0_73, plain, (k4_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_37, c_0_18]), ['final']).
% 0.12/0.37  cnf(c_0_74, negated_conjecture, (r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|k2_struct_0(esk1_0)!=k4_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_57]), ['final']).
% 0.12/0.37  cnf(c_0_75, negated_conjecture, (k2_struct_0(esk1_0)=k4_xboole_0(esk2_0,esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_48]), ['final']).
% 0.12/0.37  cnf(c_0_76, negated_conjecture, (u1_struct_0(esk1_0)=esk2_0|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_58, c_0_24]), ['final']).
% 0.12/0.37  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk1_0)=esk3_0|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_23]), ['final']).
% 0.12/0.37  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_59]), ['final']).
% 0.12/0.37  cnf(c_0_79, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_60, c_0_61]), ['final']).
% 0.12/0.37  cnf(c_0_80, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.12/0.37  # SZS output end Saturation
% 0.12/0.37  # Proof object total steps             : 81
% 0.12/0.37  # Proof object clause steps            : 60
% 0.12/0.37  # Proof object formula steps           : 21
% 0.12/0.37  # Proof object conjectures             : 26
% 0.12/0.37  # Proof object clause conjectures      : 23
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 18
% 0.12/0.37  # Proof object initial formulas used   : 10
% 0.12/0.37  # Proof object generating inferences   : 37
% 0.12/0.37  # Proof object simplifying inferences  : 17
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 19
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 18
% 0.12/0.37  # Processed clauses                    : 214
% 0.12/0.37  # ...of these trivial                  : 3
% 0.12/0.37  # ...subsumed                          : 137
% 0.12/0.37  # ...remaining for further processing  : 74
% 0.12/0.37  # Other redundant clauses eliminated   : 2
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 2
% 0.12/0.37  # Generated clauses                    : 206
% 0.12/0.37  # ...of the previous two non-trivial   : 180
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 204
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 2
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 53
% 0.12/0.37  #    Positive orientable unit clauses  : 13
% 0.12/0.37  #    Positive unorientable unit clauses: 1
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 38
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 20
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 757
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 389
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 136
% 0.12/0.37  # Unit Clause-clause subsumption calls : 1
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 8
% 0.12/0.37  # BW rewrite match successes           : 4
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4317
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.034 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.038 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
