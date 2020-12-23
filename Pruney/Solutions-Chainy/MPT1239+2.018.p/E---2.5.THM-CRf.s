%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:56 EST 2020

% Result     : Theorem 8.81s
% Output     : CNFRefutation 8.81s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 232 expanded)
%              Number of clauses        :   56 ( 110 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  197 ( 671 expanded)
%              Number of equality atoms :   21 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_tops_1])).

fof(c_0_13,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_xboole_0(X19,X21)
      | r1_tarski(X19,k4_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

fof(c_0_14,plain,(
    ! [X6,X7,X8] :
      ( ( r1_tarski(X6,X7)
        | ~ r1_tarski(X6,k4_xboole_0(X7,X8)) )
      & ( r1_xboole_0(X6,X8)
        | ~ r1_tarski(X6,k4_xboole_0(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_15,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | r1_tarski(k1_tops_1(X27,X28),X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k4_xboole_0(X4,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X16,X17,X18] :
      ( ( r1_xboole_0(X16,k2_xboole_0(X17,X18))
        | ~ r1_xboole_0(X16,X17)
        | ~ r1_xboole_0(X16,X18) )
      & ( r1_xboole_0(X16,X17)
        | ~ r1_xboole_0(X16,k2_xboole_0(X17,X18)) )
      & ( r1_xboole_0(X16,X18)
        | ~ r1_xboole_0(X16,k2_xboole_0(X17,X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_34,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X29,X30,X31] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ r1_tarski(X30,X31)
      | r1_tarski(k1_tops_1(X29,X30),k1_tops_1(X29,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X2)
    | ~ r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))
    | ~ r1_tarski(k4_xboole_0(X3,X2),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,k2_xboole_0(X2,X4))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_19])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | k7_subset_1(X22,X23,X24) = k4_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),X1)
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X2)
    | ~ r1_tarski(k4_xboole_0(X3,X2),X1)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33])).

cnf(c_0_49,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k4_xboole_0(X4,k2_xboole_0(X3,X5)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_43])).

fof(c_0_51,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_54,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_29])])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X3)
    | ~ r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X4,X2))
    | ~ r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4) ),
    inference(spm,[status(thm)],[c_0_50,c_0_26])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_23])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_62,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_23])).

cnf(c_0_63,plain,
    ( k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_26])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_42])])).

cnf(c_0_66,negated_conjecture,
    ( k2_xboole_0(k1_tops_1(esk1_0,esk3_0),esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_39]),c_0_37])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),X1) = k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k1_tops_1(esk1_0,esk3_0)),esk3_0) = k4_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ r1_tarski(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(X1,k4_xboole_0(X2,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X2))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_42])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k4_xboole_0(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_42])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,X2))
    | ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(k4_xboole_0(X1,X2),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_47])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_26])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_26])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_79])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 8.81/9.03  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S050I
% 8.81/9.03  # and selection function PSelectNewComplexExceptUniqMaxHorn.
% 8.81/9.03  #
% 8.81/9.03  # Preprocessing time       : 0.027 s
% 8.81/9.03  # Presaturation interreduction done
% 8.81/9.03  
% 8.81/9.03  # Proof found!
% 8.81/9.03  # SZS status Theorem
% 8.81/9.03  # SZS output start CNFRefutation
% 8.81/9.03  fof(t50_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 8.81/9.03  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 8.81/9.03  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 8.81/9.03  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.81/9.03  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.81/9.03  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.81/9.03  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 8.81/9.03  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.81/9.03  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.81/9.03  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 8.81/9.03  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.81/9.03  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.81/9.03  fof(c_0_12, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t50_tops_1])).
% 8.81/9.03  fof(c_0_13, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_xboole_0(X19,X21)|r1_tarski(X19,k4_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 8.81/9.03  fof(c_0_14, plain, ![X6, X7, X8]:((r1_tarski(X6,X7)|~r1_tarski(X6,k4_xboole_0(X7,X8)))&(r1_xboole_0(X6,X8)|~r1_tarski(X6,k4_xboole_0(X7,X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 8.81/9.03  fof(c_0_15, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 8.81/9.03  fof(c_0_16, plain, ![X25, X26]:((~m1_subset_1(X25,k1_zfmisc_1(X26))|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|m1_subset_1(X25,k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 8.81/9.03  fof(c_0_17, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 8.81/9.03  cnf(c_0_18, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 8.81/9.03  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 8.81/9.03  cnf(c_0_20, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 8.81/9.03  fof(c_0_21, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 8.81/9.03  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 8.81/9.03  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 8.81/9.03  fof(c_0_24, plain, ![X27, X28]:(~l1_pre_topc(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|r1_tarski(k1_tops_1(X27,X28),X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 8.81/9.03  cnf(c_0_25, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,k4_xboole_0(X4,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 8.81/9.03  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_20])).
% 8.81/9.03  fof(c_0_27, plain, ![X16, X17, X18]:((r1_xboole_0(X16,k2_xboole_0(X17,X18))|~r1_xboole_0(X16,X17)|~r1_xboole_0(X16,X18))&((r1_xboole_0(X16,X17)|~r1_xboole_0(X16,k2_xboole_0(X17,X18)))&(r1_xboole_0(X16,X18)|~r1_xboole_0(X16,k2_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 8.81/9.03  cnf(c_0_28, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 8.81/9.03  cnf(c_0_29, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 8.81/9.03  cnf(c_0_30, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 8.81/9.03  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 8.81/9.03  cnf(c_0_32, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 8.81/9.03  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 8.81/9.03  fof(c_0_34, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 8.81/9.03  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 8.81/9.03  fof(c_0_36, plain, ![X29, X30, X31]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|(~r1_tarski(X30,X31)|r1_tarski(k1_tops_1(X29,X30),k1_tops_1(X29,X31)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 8.81/9.03  cnf(c_0_37, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 8.81/9.03  cnf(c_0_38, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 8.81/9.03  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 8.81/9.03  cnf(c_0_40, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X3,X2)|~r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))|~r1_tarski(k4_xboole_0(X3,X2),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 8.81/9.03  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 8.81/9.03  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 8.81/9.03  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,k2_xboole_0(X2,X4)))), inference(spm,[status(thm)],[c_0_35, c_0_19])).
% 8.81/9.03  cnf(c_0_44, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 8.81/9.03  fof(c_0_45, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|k7_subset_1(X22,X23,X24)=k4_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 8.81/9.03  cnf(c_0_46, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_37])).
% 8.81/9.03  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),X1)|~r1_tarski(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 8.81/9.03  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X3,X2)|~r1_tarski(k4_xboole_0(X3,X2),X1)|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_40, c_0_33])).
% 8.81/9.03  cnf(c_0_49, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 8.81/9.03  cnf(c_0_50, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,k4_xboole_0(X4,k2_xboole_0(X3,X5)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_43])).
% 8.81/9.03  fof(c_0_51, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 8.81/9.03  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 8.81/9.03  cnf(c_0_53, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_31])).
% 8.81/9.03  cnf(c_0_54, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 8.81/9.03  cnf(c_0_55, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_29])])).
% 8.81/9.03  cnf(c_0_56, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X3)|~r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 8.81/9.03  cnf(c_0_57, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X4,X2))|~r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4)), inference(spm,[status(thm)],[c_0_50, c_0_26])).
% 8.81/9.03  cnf(c_0_58, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 8.81/9.03  cnf(c_0_59, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_52])).
% 8.81/9.03  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_53, c_0_23])).
% 8.81/9.03  cnf(c_0_61, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 8.81/9.03  cnf(c_0_62, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_23])).
% 8.81/9.03  cnf(c_0_63, plain, (k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_54, c_0_39])).
% 8.81/9.03  cnf(c_0_64, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_55, c_0_26])).
% 8.81/9.03  cnf(c_0_65, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_42])])).
% 8.81/9.03  cnf(c_0_66, negated_conjecture, (k2_xboole_0(k1_tops_1(esk1_0,esk3_0),esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 8.81/9.03  cnf(c_0_67, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk2_0))|~r1_tarski(X1,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_39]), c_0_37])).
% 8.81/9.03  cnf(c_0_68, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 8.81/9.03  cnf(c_0_69, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),X1)=k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 8.81/9.03  cnf(c_0_70, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k1_tops_1(esk1_0,esk3_0)),esk3_0)=k4_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 8.81/9.03  cnf(c_0_71, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~r1_tarski(X1,k1_tops_1(esk1_0,X2))|~r1_tarski(X2,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_67])).
% 8.81/9.03  cnf(c_0_72, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 8.81/9.03  cnf(c_0_73, negated_conjecture, (r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,esk3_0)))|~r1_tarski(X1,k4_xboole_0(X2,esk3_0))), inference(spm,[status(thm)],[c_0_41, c_0_70])).
% 8.81/9.03  cnf(c_0_74, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~r1_tarski(X1,k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X2)))), inference(spm,[status(thm)],[c_0_71, c_0_42])).
% 8.81/9.03  cnf(c_0_75, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k4_xboole_0(esk2_0,X2))), inference(spm,[status(thm)],[c_0_46, c_0_42])).
% 8.81/9.03  cnf(c_0_76, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 8.81/9.03  cnf(c_0_77, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,X2))|~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,X2)),X3)|~r1_tarski(k4_xboole_0(X1,X2),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_25, c_0_47])).
% 8.81/9.03  cnf(c_0_78, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_74, c_0_26])).
% 8.81/9.03  cnf(c_0_79, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_75, c_0_26])).
% 8.81/9.03  cnf(c_0_80, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_79])]), ['proof']).
% 8.81/9.03  # SZS output end CNFRefutation
% 8.81/9.03  # Proof object total steps             : 81
% 8.81/9.03  # Proof object clause steps            : 56
% 8.81/9.03  # Proof object formula steps           : 25
% 8.81/9.03  # Proof object conjectures             : 33
% 8.81/9.03  # Proof object clause conjectures      : 30
% 8.81/9.03  # Proof object formula conjectures     : 3
% 8.81/9.03  # Proof object initial clauses used    : 18
% 8.81/9.03  # Proof object initial formulas used   : 12
% 8.81/9.03  # Proof object generating inferences   : 35
% 8.81/9.03  # Proof object simplifying inferences  : 11
% 8.81/9.03  # Training examples: 0 positive, 0 negative
% 8.81/9.03  # Parsed axioms                        : 12
% 8.81/9.03  # Removed by relevancy pruning/SinE    : 0
% 8.81/9.03  # Initial clauses                      : 22
% 8.81/9.03  # Removed in clause preprocessing      : 0
% 8.81/9.03  # Initial clauses in saturation        : 22
% 8.81/9.03  # Processed clauses                    : 31435
% 8.81/9.03  # ...of these trivial                  : 1354
% 8.81/9.03  # ...subsumed                          : 21777
% 8.81/9.03  # ...remaining for further processing  : 8304
% 8.81/9.03  # Other redundant clauses eliminated   : 2
% 8.81/9.03  # Clauses deleted for lack of memory   : 0
% 8.81/9.03  # Backward-subsumed                    : 424
% 8.81/9.03  # Backward-rewritten                   : 204
% 8.81/9.03  # Generated clauses                    : 1101479
% 8.81/9.03  # ...of the previous two non-trivial   : 1047218
% 8.81/9.03  # Contextual simplify-reflections      : 36
% 8.81/9.03  # Paramodulations                      : 1101477
% 8.81/9.03  # Factorizations                       : 0
% 8.81/9.03  # Equation resolutions                 : 2
% 8.81/9.03  # Propositional unsat checks           : 0
% 8.81/9.03  #    Propositional check models        : 0
% 8.81/9.03  #    Propositional check unsatisfiable : 0
% 8.81/9.03  #    Propositional clauses             : 0
% 8.81/9.03  #    Propositional clauses after purity: 0
% 8.81/9.03  #    Propositional unsat core size     : 0
% 8.81/9.03  #    Propositional preprocessing time  : 0.000
% 8.81/9.03  #    Propositional encoding time       : 0.000
% 8.81/9.03  #    Propositional solver time         : 0.000
% 8.81/9.03  #    Success case prop preproc time    : 0.000
% 8.81/9.03  #    Success case prop encoding time   : 0.000
% 8.81/9.03  #    Success case prop solver time     : 0.000
% 8.81/9.03  # Current number of processed clauses  : 7653
% 8.81/9.03  #    Positive orientable unit clauses  : 1031
% 8.81/9.03  #    Positive unorientable unit clauses: 0
% 8.81/9.03  #    Negative unit clauses             : 2
% 8.81/9.03  #    Non-unit-clauses                  : 6620
% 8.81/9.03  # Current number of unprocessed clauses: 1015250
% 8.81/9.03  # ...number of literals in the above   : 3755042
% 8.81/9.03  # Current number of archived formulas  : 0
% 8.81/9.03  # Current number of archived clauses   : 649
% 8.81/9.03  # Clause-clause subsumption calls (NU) : 5432881
% 8.81/9.03  # Rec. Clause-clause subsumption calls : 3942639
% 8.81/9.03  # Non-unit clause-clause subsumptions  : 22237
% 8.81/9.03  # Unit Clause-clause subsumption calls : 57835
% 8.81/9.03  # Rewrite failures with RHS unbound    : 0
% 8.81/9.03  # BW rewrite match attempts            : 15844
% 8.81/9.03  # BW rewrite match successes           : 153
% 8.81/9.03  # Condensation attempts                : 0
% 8.81/9.03  # Condensation successes               : 0
% 8.81/9.03  # Termbank termtop insertions          : 28876820
% 8.90/9.06  
% 8.90/9.06  # -------------------------------------------------
% 8.90/9.06  # User time                : 8.347 s
% 8.90/9.06  # System time              : 0.365 s
% 8.90/9.06  # Total time               : 8.712 s
% 8.90/9.06  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
