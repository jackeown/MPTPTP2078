%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:57 EST 2020

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 169 expanded)
%              Number of clauses        :   45 (  75 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 ( 460 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   10 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X29,k1_zfmisc_1(X30))
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | m1_subset_1(X29,k1_zfmisc_1(X30)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ~ r1_tarski(k1_tops_1(esk2_0,k7_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0)),k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_16,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X13,X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | r1_tarski(k1_tops_1(X31,X32),X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_20,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | r1_xboole_0(X20,k4_xboole_0(X22,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_25,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(X10,X11)
      | r1_xboole_0(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

fof(c_0_35,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_xboole_0(X18,X19)
      | r1_xboole_0(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_40,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_xboole_0(X23,X25)
      | r1_tarski(X23,k4_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(esk2_0,esk4_0),k4_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_34])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_45,plain,(
    ! [X33,X34,X35] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ r1_tarski(X34,X35)
      | r1_tarski(k1_tops_1(X33,X34),k1_tops_1(X33,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

fof(c_0_46,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | k7_subset_1(X26,X27,X28) = k4_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_28])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk4_0),k1_tops_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_41])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),k4_xboole_0(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_44]),c_0_28])])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk4_0),k4_xboole_0(X2,k1_tops_1(esk2_0,esk4_0)))
    | ~ r1_tarski(k4_xboole_0(X1,esk4_0),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_18]),c_0_28])])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk2_0,k7_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0)),k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_59,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk4_0),k4_xboole_0(X1,k1_tops_1(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_33])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),k4_xboole_0(X2,X1))
    | ~ r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),k1_tops_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_44]),c_0_33])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),X1) = k4_xboole_0(k1_tops_1(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk2_0,esk4_0)))
    | ~ r1_tarski(X1,k4_xboole_0(X2,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),k4_xboole_0(k1_tops_1(esk2_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:19:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.93/1.10  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03AN
% 0.93/1.10  # and selection function SelectComplex.
% 0.93/1.10  #
% 0.93/1.10  # Preprocessing time       : 0.027 s
% 0.93/1.10  # Presaturation interreduction done
% 0.93/1.10  
% 0.93/1.10  # Proof found!
% 0.93/1.10  # SZS status Theorem
% 0.93/1.10  # SZS output start CNFRefutation
% 0.93/1.10  fof(t50_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tops_1)).
% 0.93/1.10  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.93/1.10  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.93/1.10  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.93/1.10  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.93/1.10  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.93/1.10  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.93/1.10  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.93/1.10  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.93/1.10  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.93/1.10  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.93/1.10  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.93/1.10  fof(c_0_12, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t50_tops_1])).
% 0.93/1.10  fof(c_0_13, plain, ![X29, X30]:((~m1_subset_1(X29,k1_zfmisc_1(X30))|r1_tarski(X29,X30))&(~r1_tarski(X29,X30)|m1_subset_1(X29,k1_zfmisc_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.93/1.10  fof(c_0_14, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&~r1_tarski(k1_tops_1(esk2_0,k7_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0)),k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.93/1.10  fof(c_0_15, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.93/1.10  fof(c_0_16, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X13,X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.93/1.10  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.93/1.10  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.93/1.10  fof(c_0_19, plain, ![X31, X32]:(~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|r1_tarski(k1_tops_1(X31,X32),X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.93/1.10  fof(c_0_20, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|r1_xboole_0(X20,k4_xboole_0(X22,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.93/1.10  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.93/1.10  cnf(c_0_22, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.93/1.10  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.93/1.10  cnf(c_0_24, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.93/1.10  fof(c_0_25, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.93/1.10  cnf(c_0_26, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.93/1.10  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.93/1.10  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.93/1.10  fof(c_0_29, plain, ![X10, X11]:(~r1_xboole_0(X10,X11)|r1_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.93/1.10  cnf(c_0_30, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.93/1.10  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.93/1.10  cnf(c_0_32, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.93/1.10  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.93/1.10  cnf(c_0_34, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.93/1.10  fof(c_0_35, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_xboole_0(X18,X19)|r1_xboole_0(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.93/1.10  cnf(c_0_36, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.93/1.10  cnf(c_0_37, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.93/1.10  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.93/1.10  cnf(c_0_39, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.93/1.10  fof(c_0_40, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_xboole_0(X23,X25)|r1_tarski(X23,k4_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.93/1.10  cnf(c_0_41, negated_conjecture, (r1_xboole_0(k1_tops_1(esk2_0,esk4_0),k4_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_34])).
% 0.93/1.10  cnf(c_0_42, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.93/1.10  cnf(c_0_43, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.93/1.10  cnf(c_0_44, negated_conjecture, (m1_subset_1(k4_xboole_0(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.93/1.10  fof(c_0_45, plain, ![X33, X34, X35]:(~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|(~r1_tarski(X34,X35)|r1_tarski(k1_tops_1(X33,X34),k1_tops_1(X33,X35)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.93/1.10  fof(c_0_46, plain, ![X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|k7_subset_1(X26,X27,X28)=k4_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.93/1.10  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_18]), c_0_28])])).
% 0.93/1.10  cnf(c_0_48, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.93/1.10  cnf(c_0_49, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,esk4_0),k1_tops_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_41])).
% 0.93/1.10  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.93/1.10  cnf(c_0_51, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),k4_xboole_0(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_44]), c_0_28])])).
% 0.93/1.10  cnf(c_0_52, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.93/1.10  cnf(c_0_53, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.93/1.10  cnf(c_0_54, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_47])).
% 0.93/1.10  cnf(c_0_55, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk4_0),k4_xboole_0(X2,k1_tops_1(esk2_0,esk4_0)))|~r1_tarski(k4_xboole_0(X1,esk4_0),X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.93/1.10  cnf(c_0_56, negated_conjecture, (r1_xboole_0(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.93/1.10  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_18]), c_0_28])])).
% 0.93/1.10  cnf(c_0_58, negated_conjecture, (~r1_tarski(k1_tops_1(esk2_0,k7_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0)),k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.93/1.10  cnf(c_0_59, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1)=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_53, c_0_18])).
% 0.93/1.10  cnf(c_0_60, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_38, c_0_54])).
% 0.93/1.10  cnf(c_0_61, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk4_0),k4_xboole_0(X1,k1_tops_1(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_55, c_0_33])).
% 0.93/1.10  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),k4_xboole_0(X2,X1))|~r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),X2)), inference(spm,[status(thm)],[c_0_48, c_0_56])).
% 0.93/1.10  cnf(c_0_63, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),k1_tops_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_44]), c_0_33])])).
% 0.93/1.10  cnf(c_0_64, negated_conjecture, (~r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0)))), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.93/1.11  cnf(c_0_65, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),X1)=k4_xboole_0(k1_tops_1(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_53, c_0_60])).
% 0.93/1.11  cnf(c_0_66, negated_conjecture, (r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk2_0,esk4_0)))|~r1_tarski(X1,k4_xboole_0(X2,esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_61])).
% 0.93/1.11  cnf(c_0_67, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),k4_xboole_0(k1_tops_1(esk2_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.93/1.11  cnf(c_0_68, negated_conjecture, (~r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0)))), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.93/1.11  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), ['proof']).
% 0.93/1.11  # SZS output end CNFRefutation
% 0.93/1.11  # Proof object total steps             : 70
% 0.93/1.11  # Proof object clause steps            : 45
% 0.93/1.11  # Proof object formula steps           : 25
% 0.93/1.11  # Proof object conjectures             : 31
% 0.93/1.11  # Proof object clause conjectures      : 28
% 0.93/1.11  # Proof object formula conjectures     : 3
% 0.93/1.11  # Proof object initial clauses used    : 17
% 0.93/1.11  # Proof object initial formulas used   : 12
% 0.93/1.11  # Proof object generating inferences   : 26
% 0.93/1.11  # Proof object simplifying inferences  : 13
% 0.93/1.11  # Training examples: 0 positive, 0 negative
% 0.93/1.11  # Parsed axioms                        : 12
% 0.93/1.11  # Removed by relevancy pruning/SinE    : 0
% 0.93/1.11  # Initial clauses                      : 19
% 0.93/1.11  # Removed in clause preprocessing      : 0
% 0.93/1.11  # Initial clauses in saturation        : 19
% 0.93/1.11  # Processed clauses                    : 4319
% 0.93/1.11  # ...of these trivial                  : 1076
% 0.93/1.11  # ...subsumed                          : 17
% 0.93/1.11  # ...remaining for further processing  : 3226
% 0.93/1.11  # Other redundant clauses eliminated   : 0
% 0.93/1.11  # Clauses deleted for lack of memory   : 0
% 0.93/1.11  # Backward-subsumed                    : 58
% 0.93/1.11  # Backward-rewritten                   : 60
% 0.93/1.11  # Generated clauses                    : 90696
% 0.93/1.11  # ...of the previous two non-trivial   : 74945
% 0.93/1.11  # Contextual simplify-reflections      : 1
% 0.93/1.11  # Paramodulations                      : 90696
% 0.93/1.11  # Factorizations                       : 0
% 0.93/1.11  # Equation resolutions                 : 0
% 0.93/1.11  # Propositional unsat checks           : 0
% 0.93/1.11  #    Propositional check models        : 0
% 0.93/1.11  #    Propositional check unsatisfiable : 0
% 0.93/1.11  #    Propositional clauses             : 0
% 0.93/1.11  #    Propositional clauses after purity: 0
% 0.93/1.11  #    Propositional unsat core size     : 0
% 0.93/1.11  #    Propositional preprocessing time  : 0.000
% 0.93/1.11  #    Propositional encoding time       : 0.000
% 0.93/1.11  #    Propositional solver time         : 0.000
% 0.93/1.11  #    Success case prop preproc time    : 0.000
% 0.93/1.11  #    Success case prop encoding time   : 0.000
% 0.93/1.11  #    Success case prop solver time     : 0.000
% 0.93/1.11  # Current number of processed clauses  : 3089
% 0.93/1.11  #    Positive orientable unit clauses  : 1787
% 0.93/1.11  #    Positive unorientable unit clauses: 0
% 0.93/1.11  #    Negative unit clauses             : 1
% 0.93/1.11  #    Non-unit-clauses                  : 1301
% 0.93/1.11  # Current number of unprocessed clauses: 70604
% 0.93/1.11  # ...number of literals in the above   : 73845
% 0.93/1.11  # Current number of archived formulas  : 0
% 0.93/1.11  # Current number of archived clauses   : 137
% 0.93/1.11  # Clause-clause subsumption calls (NU) : 106963
% 0.93/1.11  # Rec. Clause-clause subsumption calls : 104257
% 0.93/1.11  # Non-unit clause-clause subsumptions  : 76
% 0.93/1.11  # Unit Clause-clause subsumption calls : 11359
% 0.93/1.11  # Rewrite failures with RHS unbound    : 0
% 0.93/1.11  # BW rewrite match attempts            : 37463
% 0.93/1.11  # BW rewrite match successes           : 60
% 0.93/1.11  # Condensation attempts                : 0
% 0.93/1.11  # Condensation successes               : 0
% 0.93/1.11  # Termbank termtop insertions          : 1958607
% 0.93/1.11  
% 0.93/1.11  # -------------------------------------------------
% 0.93/1.11  # User time                : 0.723 s
% 0.93/1.11  # System time              : 0.040 s
% 0.93/1.11  # Total time               : 0.764 s
% 0.93/1.11  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
