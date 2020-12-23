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
% DateTime   : Thu Dec  3 11:10:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 225 expanded)
%              Number of clauses        :   45 ( 101 expanded)
%              Number of leaves         :   14 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  167 ( 576 expanded)
%              Number of equality atoms :    7 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   2 average)
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

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t75_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

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

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_tops_1])).

fof(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_16,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | k7_subset_1(X26,X27,X28) = k4_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_17,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_18,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | r1_xboole_0(X20,k4_xboole_0(X22,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_19,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X29,k1_zfmisc_1(X30))
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | m1_subset_1(X29,k1_zfmisc_1(X30)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_20,plain,(
    ! [X6,X7,X8] :
      ( ( r1_tarski(X6,X7)
        | ~ r1_tarski(X6,k4_xboole_0(X7,X8)) )
      & ( r1_xboole_0(X6,X8)
        | ~ r1_tarski(X6,k4_xboole_0(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_21,plain,(
    ! [X9,X10] : r1_tarski(k3_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X18,X19] :
      ( ( ~ r1_xboole_0(X18,X19)
        | k4_xboole_0(X18,X19) = X18 )
      & ( k4_xboole_0(X18,X19) != X18
        | r1_xboole_0(X18,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_28,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | r1_tarski(k1_tops_1(X31,X32),X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_29,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_31,plain,(
    ! [X16,X17] :
      ( r1_xboole_0(X16,X17)
      | ~ r1_xboole_0(k3_xboole_0(X16,X17),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

fof(c_0_35,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_xboole_0(X23,X25)
      | r1_tarski(X23,k4_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_36,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_24])).

fof(c_0_43,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k3_xboole_0(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_55,plain,(
    ! [X33,X34,X35] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ r1_tarski(X34,X35)
      | r1_tarski(k1_tops_1(X33,X34),k1_tops_1(X33,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_24]),c_0_40])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_37])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_40]),c_0_24]),c_0_51])])).

cnf(c_0_65,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k4_xboole_0(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_xboole_0(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_65]),c_0_69])])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k1_tops_1(X1,k4_xboole_0(X2,X3)),X3)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k4_xboole_0(X2,X3),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_40]),c_0_69])]),
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
% 0.12/0.34  % DateTime   : Tue Dec  1 18:49:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.49  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.49  #
% 0.19/0.49  # Preprocessing time       : 0.028 s
% 0.19/0.49  # Presaturation interreduction done
% 0.19/0.49  
% 0.19/0.49  # Proof found!
% 0.19/0.49  # SZS status Theorem
% 0.19/0.49  # SZS output start CNFRefutation
% 0.19/0.49  fof(t50_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 0.19/0.49  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.19/0.49  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.49  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.19/0.49  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.49  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.19/0.49  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.49  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.49  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.19/0.49  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.49  fof(t75_xboole_1, axiom, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.19/0.49  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.19/0.49  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.49  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.19/0.49  fof(c_0_14, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t50_tops_1])).
% 0.19/0.49  fof(c_0_15, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.49  fof(c_0_16, plain, ![X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|k7_subset_1(X26,X27,X28)=k4_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.19/0.49  fof(c_0_17, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.49  fof(c_0_18, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|r1_xboole_0(X20,k4_xboole_0(X22,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.19/0.49  fof(c_0_19, plain, ![X29, X30]:((~m1_subset_1(X29,k1_zfmisc_1(X30))|r1_tarski(X29,X30))&(~r1_tarski(X29,X30)|m1_subset_1(X29,k1_zfmisc_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.49  fof(c_0_20, plain, ![X6, X7, X8]:((r1_tarski(X6,X7)|~r1_tarski(X6,k4_xboole_0(X7,X8)))&(r1_xboole_0(X6,X8)|~r1_tarski(X6,k4_xboole_0(X7,X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.19/0.49  fof(c_0_21, plain, ![X9, X10]:r1_tarski(k3_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.49  cnf(c_0_22, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_23, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.49  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_25, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.49  cnf(c_0_26, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.49  fof(c_0_27, plain, ![X18, X19]:((~r1_xboole_0(X18,X19)|k4_xboole_0(X18,X19)=X18)&(k4_xboole_0(X18,X19)!=X18|r1_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.49  fof(c_0_28, plain, ![X31, X32]:(~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|r1_tarski(k1_tops_1(X31,X32),X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.19/0.49  fof(c_0_29, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.49  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.49  fof(c_0_31, plain, ![X16, X17]:(r1_xboole_0(X16,X17)|~r1_xboole_0(k3_xboole_0(X16,X17),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).
% 0.19/0.49  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.49  cnf(c_0_33, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.49  cnf(c_0_34, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.19/0.49  fof(c_0_35, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_xboole_0(X23,X25)|r1_tarski(X23,k4_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.19/0.49  cnf(c_0_36, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.49  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.49  cnf(c_0_38, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.49  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_41, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.49  cnf(c_0_42, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_30, c_0_24])).
% 0.19/0.49  fof(c_0_43, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.49  cnf(c_0_44, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k3_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.49  cnf(c_0_45, plain, (r1_xboole_0(k3_xboole_0(k4_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.49  cnf(c_0_46, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_34, c_0_23])).
% 0.19/0.49  cnf(c_0_47, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.49  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X2,X3)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.49  cnf(c_0_49, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.19/0.49  cnf(c_0_50, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.49  cnf(c_0_51, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.49  cnf(c_0_52, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.49  cnf(c_0_53, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0))|~r1_xboole_0(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.49  cnf(c_0_54, negated_conjecture, (r1_xboole_0(X1,k1_tops_1(esk1_0,esk3_0))|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.49  fof(c_0_55, plain, ![X33, X34, X35]:(~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|(~r1_tarski(X34,X35)|r1_tarski(k1_tops_1(X33,X34),k1_tops_1(X33,X35)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.19/0.49  cnf(c_0_56, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_50])).
% 0.19/0.49  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_24]), c_0_40])])).
% 0.19/0.49  cnf(c_0_58, plain, (r1_tarski(X1,X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_51, c_0_37])).
% 0.19/0.49  cnf(c_0_59, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_25, c_0_52])).
% 0.19/0.49  cnf(c_0_60, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0))|~r1_xboole_0(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.49  cnf(c_0_61, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.49  cnf(c_0_62, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.49  cnf(c_0_63, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.49  cnf(c_0_64, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_xboole_0(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_40]), c_0_24]), c_0_51])])).
% 0.19/0.49  cnf(c_0_65, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.49  cnf(c_0_66, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.49  cnf(c_0_67, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k4_xboole_0(esk2_0,X2))), inference(spm,[status(thm)],[c_0_56, c_0_51])).
% 0.19/0.49  cnf(c_0_68, negated_conjecture, (~m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_xboole_0(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 0.19/0.49  cnf(c_0_69, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_67, c_0_63])).
% 0.19/0.49  cnf(c_0_70, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_38, c_0_65])).
% 0.19/0.49  cnf(c_0_71, negated_conjecture, (~r1_xboole_0(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_65]), c_0_69])])).
% 0.19/0.49  cnf(c_0_72, plain, (r1_xboole_0(k1_tops_1(X1,k4_xboole_0(X2,X3)),X3)|~l1_pre_topc(X1)|~r1_tarski(k4_xboole_0(X2,X3),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_32, c_0_70])).
% 0.19/0.49  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_40]), c_0_69])]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 74
% 0.19/0.49  # Proof object clause steps            : 45
% 0.19/0.49  # Proof object formula steps           : 29
% 0.19/0.49  # Proof object conjectures             : 25
% 0.19/0.49  # Proof object clause conjectures      : 22
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 18
% 0.19/0.49  # Proof object initial formulas used   : 14
% 0.19/0.49  # Proof object generating inferences   : 27
% 0.19/0.49  # Proof object simplifying inferences  : 17
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 14
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 21
% 0.19/0.49  # Removed in clause preprocessing      : 0
% 0.19/0.49  # Initial clauses in saturation        : 21
% 0.19/0.49  # Processed clauses                    : 1612
% 0.19/0.49  # ...of these trivial                  : 29
% 0.19/0.49  # ...subsumed                          : 976
% 0.19/0.49  # ...remaining for further processing  : 607
% 0.19/0.49  # Other redundant clauses eliminated   : 0
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 63
% 0.19/0.49  # Backward-rewritten                   : 9
% 0.19/0.49  # Generated clauses                    : 6106
% 0.19/0.50  # ...of the previous two non-trivial   : 5630
% 0.19/0.50  # Contextual simplify-reflections      : 20
% 0.19/0.50  # Paramodulations                      : 6106
% 0.19/0.50  # Factorizations                       : 0
% 0.19/0.50  # Equation resolutions                 : 0
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
% 0.19/0.50  # Current number of processed clauses  : 514
% 0.19/0.50  #    Positive orientable unit clauses  : 90
% 0.19/0.50  #    Positive unorientable unit clauses: 0
% 0.19/0.50  #    Negative unit clauses             : 19
% 0.19/0.50  #    Non-unit-clauses                  : 405
% 0.19/0.50  # Current number of unprocessed clauses: 3988
% 0.19/0.50  # ...number of literals in the above   : 11806
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 93
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 48914
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 28203
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 662
% 0.19/0.50  # Unit Clause-clause subsumption calls : 845
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 82
% 0.19/0.50  # BW rewrite match successes           : 6
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 81909
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.149 s
% 0.19/0.50  # System time              : 0.008 s
% 0.19/0.50  # Total time               : 0.157 s
% 0.19/0.50  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
