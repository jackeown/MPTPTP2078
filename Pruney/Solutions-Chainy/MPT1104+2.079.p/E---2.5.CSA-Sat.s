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
% DateTime   : Thu Dec  3 11:08:59 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 463 expanded)
%              Number of clauses        :   50 ( 202 expanded)
%              Number of leaves         :    8 ( 119 expanded)
%              Depth                    :    8
%              Number of atoms          :  154 (1075 expanded)
%              Number of equality atoms :   63 ( 510 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    6 (   2 average)
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

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

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

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

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

fof(c_0_8,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | k4_subset_1(X14,X15,X16) = k2_xboole_0(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_9,plain,(
    ! [X12,X13] : k3_tarski(k2_tarski(X12,X13)) = k2_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),X9) = k4_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_11,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

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
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

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
    ( k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14]),
    [final]).

cnf(c_0_20,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_14]),c_0_14]),
    [final]).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( ( ~ r1_xboole_0(X10,X11)
        | k4_xboole_0(X10,X11) = X10 )
      & ( k4_xboole_0(X10,X11) != X10
        | r1_xboole_0(X10,X11) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_22,negated_conjecture,
    ( k2_struct_0(esk1_0) = k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_23,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_18]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_26,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20]),
    [final]).

fof(c_0_27,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( k4_subset_1(X1,esk2_0,esk3_0) = k2_struct_0(esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),
    [final]).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_31,plain,
    ( k4_xboole_0(k4_subset_1(X1,X2,X3),X2) = k4_xboole_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_18]),
    [final]).

fof(c_0_32,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | k7_subset_1(X17,X18,X19) = k4_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k4_subset_1(X1,X2,X3),X3) = k4_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18]),
    [final]).

cnf(c_0_34,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_35,plain,
    ( r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)
    | k3_tarski(k2_tarski(X1,X2)) != k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_26]),
    [final]).

cnf(c_0_36,plain,
    ( r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)
    | k3_tarski(k2_tarski(X1,X2)) != k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,esk3_0)) = k2_struct_0(esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_29])).

cnf(c_0_38,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k4_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_19]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(k2_struct_0(esk1_0),esk2_0) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_22]),c_0_24]),c_0_25])]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_41,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(k2_struct_0(esk1_0),esk3_0) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_24]),c_0_25])]),
    [final]).

cnf(c_0_43,plain,
    ( k4_subset_1(X1,X2,X3) = k3_tarski(k2_tarski(X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18]),
    [final]).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))
    | k3_tarski(k2_tarski(X1,X2)) != k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35]),
    [final]).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,k3_tarski(k2_tarski(X2,X1)))
    | k3_tarski(k2_tarski(X2,X1)) != k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,esk3_0)) = k2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_24]),c_0_25])]),
    [final]).

cnf(c_0_47,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k4_xboole_0(X2,X1)
    | ~ r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_20]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(k2_struct_0(esk1_0),esk2_0)
    | k2_struct_0(esk1_0) != k4_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_39]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(k2_struct_0(esk1_0),esk2_0) != esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(k2_struct_0(esk1_0),esk3_0)
    | k2_struct_0(esk1_0) != k4_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_52,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_43]),
    [final]).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,k4_subset_1(X2,X1,X3))
    | k4_subset_1(X2,X1,X3) != k4_xboole_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_18]),
    [final]).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,k4_subset_1(X2,X3,X1))
    | k4_subset_1(X2,X3,X1) != k4_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_18]),
    [final]).

cnf(c_0_55,plain,
    ( r1_xboole_0(k4_subset_1(X1,X2,X3),X2)
    | k4_subset_1(X1,X2,X3) != k4_xboole_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_18]),
    [final]).

cnf(c_0_56,plain,
    ( r1_xboole_0(k4_subset_1(X1,X2,X3),X3)
    | k4_subset_1(X1,X2,X3) != k4_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_18]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( k4_subset_1(X1,esk3_0,esk2_0) = k2_struct_0(esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_46]),
    [final]).

cnf(c_0_58,plain,
    ( k4_subset_1(X1,X2,X3) = k4_xboole_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_18]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(esk2_0,k2_struct_0(esk1_0))
    | k2_struct_0(esk1_0) != k4_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_48]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( k2_struct_0(esk1_0) = k4_xboole_0(esk3_0,esk2_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_39]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) != esk3_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_39]),
    [final]).

cnf(c_0_62,plain,
    ( k4_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k4_subset_1(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_18]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_struct_0(esk1_0))
    | k2_struct_0(esk1_0) != k4_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_50]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( k2_struct_0(esk1_0) = k4_xboole_0(esk2_0,esk3_0)
    | ~ r1_xboole_0(k2_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_42]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_51]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.13/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.38  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.13/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.38  fof(t25_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_pre_topc)).
% 0.13/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.38  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.13/0.38  fof(c_0_8, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|~m1_subset_1(X16,k1_zfmisc_1(X14))|k4_subset_1(X14,X15,X16)=k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.13/0.38  fof(c_0_9, plain, ![X12, X13]:k3_tarski(k2_tarski(X12,X13))=k2_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.38  fof(c_0_10, plain, ![X8, X9]:k4_xboole_0(k2_xboole_0(X8,X9),X9)=k4_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t25_pre_topc])).
% 0.13/0.38  cnf(c_0_13, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_15, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_17, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((k2_struct_0(esk1_0)=k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)&r1_xboole_0(esk2_0,esk3_0))&esk3_0!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.13/0.38  cnf(c_0_18, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.13/0.38  cnf(c_0_19, plain, (k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_14]), ['final']).
% 0.13/0.38  cnf(c_0_20, plain, (k3_tarski(k2_tarski(X1,X2))=k3_tarski(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_14]), c_0_14]), ['final']).
% 0.13/0.38  fof(c_0_21, plain, ![X10, X11]:((~r1_xboole_0(X10,X11)|k4_xboole_0(X10,X11)=X10)&(k4_xboole_0(X10,X11)!=X10|r1_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (k2_struct_0(esk1_0)=k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_23, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_18, c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_26, plain, (k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.13/0.38  fof(c_0_27, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.38  cnf(c_0_28, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (k4_subset_1(X1,esk2_0,esk3_0)=k2_struct_0(esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])]), ['final']).
% 0.13/0.38  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_31, plain, (k4_xboole_0(k4_subset_1(X1,X2,X3),X2)=k4_xboole_0(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_18]), ['final']).
% 0.13/0.38  fof(c_0_32, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|k7_subset_1(X17,X18,X19)=k4_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.13/0.38  cnf(c_0_33, plain, (k4_xboole_0(k4_subset_1(X1,X2,X3),X3)=k4_xboole_0(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_34, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.13/0.38  cnf(c_0_35, plain, (r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)|k3_tarski(k2_tarski(X1,X2))!=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_26]), ['final']).
% 0.13/0.38  cnf(c_0_36, plain, (r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)|k3_tarski(k2_tarski(X1,X2))!=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_19]), ['final']).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,esk3_0))=k2_struct_0(esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_18, c_0_29])).
% 0.13/0.38  cnf(c_0_38, plain, (k3_tarski(k2_tarski(X1,X2))=k4_xboole_0(X1,X2)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_30, c_0_19]), ['final']).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (k4_xboole_0(k2_struct_0(esk1_0),esk2_0)=k4_xboole_0(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_22]), c_0_24]), c_0_25])]), ['final']).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (esk3_0!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_41, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k4_xboole_0(k2_struct_0(esk1_0),esk3_0)=k4_xboole_0(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_24]), c_0_25])]), ['final']).
% 0.13/0.38  cnf(c_0_43, plain, (k4_subset_1(X1,X2,X3)=k3_tarski(k2_tarski(X3,X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_44, plain, (r1_xboole_0(X1,k3_tarski(k2_tarski(X1,X2)))|k3_tarski(k2_tarski(X1,X2))!=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35]), ['final']).
% 0.13/0.38  cnf(c_0_45, plain, (r1_xboole_0(X1,k3_tarski(k2_tarski(X2,X1)))|k3_tarski(k2_tarski(X2,X1))!=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_36]), ['final']).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,esk3_0))=k2_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_24]), c_0_25])]), ['final']).
% 0.13/0.38  cnf(c_0_47, plain, (k3_tarski(k2_tarski(X1,X2))=k4_xboole_0(X2,X1)|~r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_38, c_0_20]), ['final']).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r1_xboole_0(k2_struct_0(esk1_0),esk2_0)|k2_struct_0(esk1_0)!=k4_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (k4_xboole_0(k2_struct_0(esk1_0),esk2_0)!=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (r1_xboole_0(k2_struct_0(esk1_0),esk3_0)|k2_struct_0(esk1_0)!=k4_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_42]), ['final']).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_52, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_18, c_0_43]), ['final']).
% 0.13/0.38  cnf(c_0_53, plain, (r1_xboole_0(X1,k4_subset_1(X2,X1,X3))|k4_subset_1(X2,X1,X3)!=k4_xboole_0(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_44, c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_54, plain, (r1_xboole_0(X1,k4_subset_1(X2,X3,X1))|k4_subset_1(X2,X3,X1)!=k4_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_45, c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_55, plain, (r1_xboole_0(k4_subset_1(X1,X2,X3),X2)|k4_subset_1(X1,X2,X3)!=k4_xboole_0(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_56, plain, (r1_xboole_0(k4_subset_1(X1,X2,X3),X3)|k4_subset_1(X1,X2,X3)!=k4_xboole_0(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (k4_subset_1(X1,esk3_0,esk2_0)=k2_struct_0(esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_46]), ['final']).
% 0.13/0.38  cnf(c_0_58, plain, (k4_subset_1(X1,X2,X3)=k4_xboole_0(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X2)), inference(spm,[status(thm)],[c_0_47, c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (r1_xboole_0(esk2_0,k2_struct_0(esk1_0))|k2_struct_0(esk1_0)!=k4_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_48]), ['final']).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (k2_struct_0(esk1_0)=k4_xboole_0(esk3_0,esk2_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)!=esk3_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[c_0_49, c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_62, plain, (k4_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k4_subset_1(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_38, c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (r1_xboole_0(esk3_0,k2_struct_0(esk1_0))|k2_struct_0(esk1_0)!=k4_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_50]), ['final']).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (k2_struct_0(esk1_0)=k4_xboole_0(esk2_0,esk3_0)|~r1_xboole_0(k2_struct_0(esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_42]), ['final']).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_51]), ['final']).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 67
% 0.13/0.38  # Proof object clause steps            : 50
% 0.13/0.38  # Proof object formula steps           : 17
% 0.13/0.38  # Proof object conjectures             : 24
% 0.13/0.38  # Proof object clause conjectures      : 21
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 8
% 0.13/0.38  # Proof object generating inferences   : 32
% 0.13/0.38  # Proof object simplifying inferences  : 16
% 0.13/0.38  # Parsed axioms                        : 8
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 14
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 13
% 0.13/0.38  # Processed clauses                    : 198
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 137
% 0.13/0.38  # ...remaining for further processing  : 59
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 197
% 0.13/0.38  # ...of the previous two non-trivial   : 172
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 197
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 44
% 0.13/0.38  #    Positive orientable unit clauses  : 11
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 31
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 16
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 549
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 283
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 136
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 7
% 0.13/0.38  # BW rewrite match successes           : 6
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3973
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.037 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
