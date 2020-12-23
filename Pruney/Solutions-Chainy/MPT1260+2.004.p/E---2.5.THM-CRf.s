%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:15 EST 2020

% Result     : Theorem 9.87s
% Output     : CNFRefutation 9.93s
% Verified   : 
% Statistics : Number of formulae       :  160 (2374 expanded)
%              Number of clauses        :  103 (1035 expanded)
%              Number of leaves         :   28 ( 594 expanded)
%              Depth                    :   24
%              Number of atoms          :  329 (5923 expanded)
%              Number of equality atoms :  101 (1754 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

fof(c_0_29,plain,(
    ! [X64,X65] :
      ( ~ l1_pre_topc(X64)
      | ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))
      | k2_tops_1(X64,X65) = k2_tops_1(X64,k3_subset_1(u1_struct_0(X64),X65)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_pre_topc(esk3_0,esk2_0)
      | k2_tops_1(esk2_0,esk3_0) != k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) )
    & ( v3_pre_topc(esk3_0,esk2_0)
      | k2_tops_1(esk2_0,esk3_0) = k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

fof(c_0_31,plain,(
    ! [X51,X52] :
      ( ( ~ m1_subset_1(X51,k1_zfmisc_1(X52))
        | r1_tarski(X51,X52) )
      & ( ~ r1_tarski(X51,X52)
        | m1_subset_1(X51,k1_zfmisc_1(X52)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_32,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | m1_subset_1(k3_subset_1(X27,X28),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_33,plain,(
    ! [X55,X56] :
      ( ~ l1_pre_topc(X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
      | m1_subset_1(k2_tops_1(X55,X56),k1_zfmisc_1(u1_struct_0(X55))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_34,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k2_tops_1(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)) = k2_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_41,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_42,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | ~ m1_subset_1(X40,k1_zfmisc_1(X38))
      | k4_subset_1(X38,X39,X40) = k2_xboole_0(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_36])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_35])).

fof(c_0_46,plain,(
    ! [X66,X67] :
      ( ~ l1_pre_topc(X66)
      | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))
      | k2_pre_topc(X66,X67) = k4_subset_1(u1_struct_0(X66),X67,k2_tops_1(X66,X67)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_47,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_48,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_49,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_50,plain,(
    ! [X21,X22] : r1_tarski(X21,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_51,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_53,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_56,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_57,plain,(
    ! [X49,X50] : k1_setfam_1(k2_tarski(X49,X50)) = k3_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk2_0),X1,k2_tops_1(esk2_0,esk3_0)) = k2_xboole_0(X1,k2_tops_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0)) = k2_pre_topc(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_35]),c_0_36])])).

fof(c_0_62,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_64,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,k2_xboole_0(X17,X18))
      | r1_tarski(k4_xboole_0(X16,X17),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_tops_1(esk2_0,esk3_0)) = k2_pre_topc(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_35]),c_0_61])).

fof(c_0_69,plain,(
    ! [X19,X20] : k2_xboole_0(k3_xboole_0(X19,X20),k4_xboole_0(X19,X20)) = X19 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_70,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_63])).

cnf(c_0_72,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_74,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,k4_xboole_0(X15,X14))
      | X14 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk3_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_68])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_78,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_79,plain,(
    ! [X23,X24] : k2_tarski(X23,X24) = k2_tarski(X24,X23) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_81,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k2_pre_topc(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_77])).

fof(c_0_85,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | k7_subset_1(X43,X44,X45) = k4_xboole_0(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_86,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_66]),c_0_73])).

cnf(c_0_87,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_88,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_54])).

cnf(c_0_89,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_82,c_0_73])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(k2_pre_topc(esk2_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_91,plain,(
    ! [X29,X30] : m1_subset_1(k6_subset_1(X29,X30),k1_zfmisc_1(X29)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_92,plain,(
    ! [X41,X42] : k6_subset_1(X41,X42) = k4_xboole_0(X41,X42) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_93,plain,(
    ! [X68,X69] :
      ( ~ l1_pre_topc(X68)
      | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
      | k1_tops_1(X68,X69) = k7_subset_1(u1_struct_0(X68),X69,k2_tops_1(X68,X69)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_94,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_95,plain,(
    ! [X53,X54] :
      ( ~ l1_pre_topc(X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
      | m1_subset_1(k2_pre_topc(X53,X54),k1_zfmisc_1(u1_struct_0(X53))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_96,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2)))) = X2 ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_97,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_88]),c_0_54])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_81])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(k2_pre_topc(esk2_0,esk3_0),X2))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_90])).

cnf(c_0_100,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_101,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_102,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_103,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_73])).

fof(c_0_104,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | k3_subset_1(X25,X26) = k4_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_105,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_106,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,X1)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_107,negated_conjecture,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_pre_topc(esk2_0,esk3_0)))) = k1_xboole_0
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_108,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_86])).

cnf(c_0_109,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101]),c_0_73])).

cnf(c_0_110,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0)) = k1_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_35]),c_0_36])])).

cnf(c_0_111,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_35])).

cnf(c_0_112,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_113,plain,
    ( k5_xboole_0(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k2_pre_topc(X1,X2),X3))) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_105])).

cnf(c_0_114,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k2_pre_topc(esk2_0,esk3_0))) = X1
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_54]),c_0_108])])).

cnf(c_0_115,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_109])).

cnf(c_0_116,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0)))) = k1_tops_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_117,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_112,c_0_73])).

fof(c_0_118,plain,(
    ! [X59,X60] :
      ( ~ l1_pre_topc(X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))
      | k2_tops_1(X59,X60) = k7_subset_1(u1_struct_0(X59),k2_pre_topc(X59,X60),k1_tops_1(X59,X60)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_119,plain,
    ( k5_xboole_0(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k2_pre_topc(X1,X2),X3))) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_44])).

cnf(c_0_120,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k2_pre_topc(esk2_0,esk3_0),X1)) = X1
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_87])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

fof(c_0_123,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | k3_subset_1(X36,k3_subset_1(X36,X37)) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_124,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_117,c_0_44])).

cnf(c_0_125,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_44])).

cnf(c_0_126,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_105])).

cnf(c_0_127,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_87])).

cnf(c_0_128,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_129,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1) = k5_xboole_0(k2_pre_topc(esk2_0,esk3_0),X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_36]),c_0_121])])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),k2_xboole_0(X1,X2))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_122])).

fof(c_0_131,plain,(
    ! [X61,X62,X63] :
      ( ~ l1_pre_topc(X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X61)))
      | ~ v3_pre_topc(X62,X61)
      | ~ r1_tarski(X62,X63)
      | r1_tarski(X62,k1_tops_1(X61,X63)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_132,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_133,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | k2_tops_1(esk2_0,esk3_0) = k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_134,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,X3)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_35]),c_0_36])])).

cnf(c_0_136,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_124,c_0_127])).

cnf(c_0_137,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)) = k2_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_36]),c_0_35]),c_0_122])])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),k2_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_68]),c_0_84])])).

cnf(c_0_139,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_140,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_132,c_0_44])).

cnf(c_0_141,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) = k2_tops_1(esk2_0,esk3_0)
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_76]),c_0_135])])).

cnf(c_0_142,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)) = k2_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_138])])).

fof(c_0_143,plain,(
    ! [X57,X58] :
      ( ~ v2_pre_topc(X57)
      | ~ l1_pre_topc(X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
      | v3_pre_topc(k1_tops_1(X57,X58),X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_144,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_35]),c_0_36])])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_121])).

cnf(c_0_146,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0)) = esk3_0
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_76])])).

cnf(c_0_147,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0)) = k1_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_142]),c_0_138])])).

cnf(c_0_148,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_143])).

cnf(c_0_149,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_150,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_44]),c_0_145])).

cnf(c_0_151,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_152,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0
    | ~ r1_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_122])).

cnf(c_0_153,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | k2_tops_1(esk2_0,esk3_0) != k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_154,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_35]),c_0_149]),c_0_36])])).

cnf(c_0_155,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_151]),c_0_84])]),c_0_152])).

cnf(c_0_156,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) != k2_tops_1(esk2_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_134]),c_0_76]),c_0_135])])).

cnf(c_0_157,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_158,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) != k2_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_156,c_0_157])])).

cnf(c_0_159,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_155]),c_0_158]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:37 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  # Version: 2.5pre002
% 0.21/0.35  # No SInE strategy applied
% 0.21/0.35  # Trying AutoSched0 for 299 seconds
% 9.87/10.08  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 9.87/10.08  # and selection function SelectMaxLComplexAvoidPosPred.
% 9.87/10.08  #
% 9.87/10.08  # Preprocessing time       : 0.042 s
% 9.87/10.08  # Presaturation interreduction done
% 9.87/10.08  
% 9.87/10.08  # Proof found!
% 9.87/10.08  # SZS status Theorem
% 9.87/10.08  # SZS output start CNFRefutation
% 9.87/10.08  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 9.87/10.08  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 9.87/10.08  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.87/10.08  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.87/10.08  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 9.87/10.08  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.87/10.08  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 9.87/10.08  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.87/10.08  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.87/10.08  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.87/10.08  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.87/10.08  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.87/10.08  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.87/10.08  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.87/10.08  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 9.87/10.08  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 9.87/10.08  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 9.87/10.08  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.87/10.08  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.87/10.08  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 9.87/10.08  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.87/10.08  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 9.87/10.08  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 9.87/10.08  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.87/10.08  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 9.87/10.08  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.87/10.08  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 9.87/10.08  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 9.87/10.08  fof(c_0_28, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 9.87/10.08  fof(c_0_29, plain, ![X64, X65]:(~l1_pre_topc(X64)|(~m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))|k2_tops_1(X64,X65)=k2_tops_1(X64,k3_subset_1(u1_struct_0(X64),X65)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 9.87/10.08  fof(c_0_30, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)!=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0))&(v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 9.87/10.08  fof(c_0_31, plain, ![X51, X52]:((~m1_subset_1(X51,k1_zfmisc_1(X52))|r1_tarski(X51,X52))&(~r1_tarski(X51,X52)|m1_subset_1(X51,k1_zfmisc_1(X52)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 9.87/10.08  fof(c_0_32, plain, ![X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|m1_subset_1(k3_subset_1(X27,X28),k1_zfmisc_1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 9.87/10.08  fof(c_0_33, plain, ![X55, X56]:(~l1_pre_topc(X55)|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|m1_subset_1(k2_tops_1(X55,X56),k1_zfmisc_1(u1_struct_0(X55)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 9.87/10.08  cnf(c_0_34, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 9.87/10.08  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.87/10.08  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.87/10.08  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.87/10.08  cnf(c_0_38, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 9.87/10.08  cnf(c_0_39, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 9.87/10.08  cnf(c_0_40, negated_conjecture, (k2_tops_1(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))=k2_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 9.87/10.08  cnf(c_0_41, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 9.87/10.08  fof(c_0_42, plain, ![X38, X39, X40]:(~m1_subset_1(X39,k1_zfmisc_1(X38))|~m1_subset_1(X40,k1_zfmisc_1(X38))|k4_subset_1(X38,X39,X40)=k2_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 9.93/10.08  cnf(c_0_43, negated_conjecture, (m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_36])])).
% 9.93/10.08  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.93/10.08  cnf(c_0_45, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_41, c_0_35])).
% 9.93/10.08  fof(c_0_46, plain, ![X66, X67]:(~l1_pre_topc(X66)|(~m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))|k2_pre_topc(X66,X67)=k4_subset_1(u1_struct_0(X66),X67,k2_tops_1(X66,X67)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 9.93/10.08  fof(c_0_47, plain, ![X10]:k2_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t1_boole])).
% 9.93/10.08  fof(c_0_48, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 9.93/10.08  fof(c_0_49, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 9.93/10.08  fof(c_0_50, plain, ![X21, X22]:r1_tarski(X21,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 9.93/10.08  cnf(c_0_51, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 9.93/10.08  cnf(c_0_52, negated_conjecture, (m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 9.93/10.08  cnf(c_0_53, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 9.93/10.08  cnf(c_0_54, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 9.93/10.08  cnf(c_0_55, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 9.93/10.08  fof(c_0_56, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 9.93/10.08  fof(c_0_57, plain, ![X49, X50]:k1_setfam_1(k2_tarski(X49,X50))=k3_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 9.93/10.08  cnf(c_0_58, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 9.93/10.08  cnf(c_0_59, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 9.93/10.08  cnf(c_0_60, negated_conjecture, (k4_subset_1(u1_struct_0(esk2_0),X1,k2_tops_1(esk2_0,esk3_0))=k2_xboole_0(X1,k2_tops_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 9.93/10.08  cnf(c_0_61, negated_conjecture, (k4_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0))=k2_pre_topc(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_35]), c_0_36])])).
% 9.93/10.08  fof(c_0_62, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 9.93/10.08  cnf(c_0_63, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 9.93/10.08  fof(c_0_64, plain, ![X16, X17, X18]:(~r1_tarski(X16,k2_xboole_0(X17,X18))|r1_tarski(k4_xboole_0(X16,X17),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 9.93/10.08  cnf(c_0_65, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 9.93/10.08  cnf(c_0_66, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 9.93/10.08  cnf(c_0_67, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 9.93/10.08  cnf(c_0_68, negated_conjecture, (k2_xboole_0(esk3_0,k2_tops_1(esk2_0,esk3_0))=k2_pre_topc(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_35]), c_0_61])).
% 9.93/10.08  fof(c_0_69, plain, ![X19, X20]:k2_xboole_0(k3_xboole_0(X19,X20),k4_xboole_0(X19,X20))=X19, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 9.93/10.08  cnf(c_0_70, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 9.93/10.08  cnf(c_0_71, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_63])).
% 9.93/10.08  cnf(c_0_72, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 9.93/10.08  cnf(c_0_73, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 9.93/10.08  fof(c_0_74, plain, ![X14, X15]:(~r1_tarski(X14,k4_xboole_0(X15,X14))|X14=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 9.93/10.08  cnf(c_0_75, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_58, c_0_67])).
% 9.93/10.08  cnf(c_0_76, negated_conjecture, (r1_tarski(esk3_0,k2_pre_topc(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_59, c_0_68])).
% 9.93/10.08  cnf(c_0_77, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_62])).
% 9.93/10.08  cnf(c_0_78, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_69])).
% 9.93/10.08  fof(c_0_79, plain, ![X23, X24]:k2_tarski(X23,X24)=k2_tarski(X24,X23), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 9.93/10.08  cnf(c_0_80, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 9.93/10.08  cnf(c_0_81, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 9.93/10.08  cnf(c_0_82, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 9.93/10.08  cnf(c_0_83, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(X1,X2))|~r1_tarski(k2_pre_topc(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 9.93/10.08  cnf(c_0_84, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_77])).
% 9.93/10.08  fof(c_0_85, plain, ![X43, X44, X45]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|k7_subset_1(X43,X44,X45)=k4_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 9.93/10.08  cnf(c_0_86, plain, (k2_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_66]), c_0_73])).
% 9.93/10.08  cnf(c_0_87, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 9.93/10.08  cnf(c_0_88, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_54])).
% 9.93/10.08  cnf(c_0_89, plain, (X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[c_0_82, c_0_73])).
% 9.93/10.08  cnf(c_0_90, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(k2_pre_topc(esk2_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 9.93/10.08  fof(c_0_91, plain, ![X29, X30]:m1_subset_1(k6_subset_1(X29,X30),k1_zfmisc_1(X29)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 9.93/10.08  fof(c_0_92, plain, ![X41, X42]:k6_subset_1(X41,X42)=k4_xboole_0(X41,X42), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 9.93/10.08  fof(c_0_93, plain, ![X68, X69]:(~l1_pre_topc(X68)|(~m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))|k1_tops_1(X68,X69)=k7_subset_1(u1_struct_0(X68),X69,k2_tops_1(X68,X69)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 9.93/10.08  cnf(c_0_94, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 9.93/10.08  fof(c_0_95, plain, ![X53, X54]:(~l1_pre_topc(X53)|~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))|m1_subset_1(k2_pre_topc(X53,X54),k1_zfmisc_1(u1_struct_0(X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 9.93/10.08  cnf(c_0_96, plain, (k2_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2))))=X2), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 9.93/10.08  cnf(c_0_97, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_88]), c_0_54])).
% 9.93/10.08  cnf(c_0_98, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))))), inference(spm,[status(thm)],[c_0_89, c_0_81])).
% 9.93/10.08  cnf(c_0_99, negated_conjecture, (r1_tarski(X1,k2_xboole_0(k2_pre_topc(esk2_0,esk3_0),X2))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_58, c_0_90])).
% 9.93/10.08  cnf(c_0_100, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 9.93/10.08  cnf(c_0_101, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 9.93/10.08  cnf(c_0_102, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 9.93/10.08  cnf(c_0_103, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_94, c_0_73])).
% 9.93/10.08  fof(c_0_104, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|k3_subset_1(X25,X26)=k4_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 9.93/10.08  cnf(c_0_105, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 9.93/10.08  cnf(c_0_106, plain, (k2_xboole_0(X1,k5_xboole_0(X2,X1))=X2|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 9.93/10.08  cnf(c_0_107, negated_conjecture, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_pre_topc(esk2_0,esk3_0))))=k1_xboole_0|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 9.93/10.08  cnf(c_0_108, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_59, c_0_86])).
% 9.93/10.08  cnf(c_0_109, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101]), c_0_73])).
% 9.93/10.08  cnf(c_0_110, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0))=k1_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_35]), c_0_36])])).
% 9.93/10.08  cnf(c_0_111, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_103, c_0_35])).
% 9.93/10.08  cnf(c_0_112, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 9.93/10.08  cnf(c_0_113, plain, (k5_xboole_0(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k2_pre_topc(X1,X2),X3)))=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_103, c_0_105])).
% 9.93/10.08  cnf(c_0_114, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k2_pre_topc(esk2_0,esk3_0)))=X1|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_54]), c_0_108])])).
% 9.93/10.08  cnf(c_0_115, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_37, c_0_109])).
% 9.93/10.08  cnf(c_0_116, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0))))=k1_tops_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_110, c_0_111])).
% 9.93/10.08  cnf(c_0_117, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_112, c_0_73])).
% 9.93/10.08  fof(c_0_118, plain, ![X59, X60]:(~l1_pre_topc(X59)|(~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))|k2_tops_1(X59,X60)=k7_subset_1(u1_struct_0(X59),k2_pre_topc(X59,X60),k1_tops_1(X59,X60)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 9.93/10.08  cnf(c_0_119, plain, (k5_xboole_0(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k2_pre_topc(X1,X2),X3)))=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3)|~l1_pre_topc(X1)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_113, c_0_44])).
% 9.93/10.08  cnf(c_0_120, negated_conjecture, (k1_setfam_1(k2_tarski(k2_pre_topc(esk2_0,esk3_0),X1))=X1|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_114, c_0_87])).
% 9.93/10.08  cnf(c_0_121, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_37, c_0_35])).
% 9.93/10.08  cnf(c_0_122, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 9.93/10.08  fof(c_0_123, plain, ![X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|k3_subset_1(X36,k3_subset_1(X36,X37))=X37), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 9.93/10.08  cnf(c_0_124, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_117, c_0_44])).
% 9.93/10.08  cnf(c_0_125, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_103, c_0_44])).
% 9.93/10.08  cnf(c_0_126, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_37, c_0_105])).
% 9.93/10.08  cnf(c_0_127, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_97, c_0_87])).
% 9.93/10.08  cnf(c_0_128, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_118])).
% 9.93/10.09  cnf(c_0_129, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1)=k5_xboole_0(k2_pre_topc(esk2_0,esk3_0),X1)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_36]), c_0_121])])).
% 9.93/10.09  cnf(c_0_130, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),k2_xboole_0(X1,X2))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_75, c_0_122])).
% 9.93/10.09  fof(c_0_131, plain, ![X61, X62, X63]:(~l1_pre_topc(X61)|(~m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X61)))|(~v3_pre_topc(X62,X61)|~r1_tarski(X62,X63)|r1_tarski(X62,k1_tops_1(X61,X63)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 9.93/10.09  cnf(c_0_132, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_123])).
% 9.93/10.09  cnf(c_0_133, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.93/10.09  cnf(c_0_134, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,X3)|~r1_tarski(X3,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 9.93/10.09  cnf(c_0_135, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_35]), c_0_36])])).
% 9.93/10.09  cnf(c_0_136, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_124, c_0_127])).
% 9.93/10.09  cnf(c_0_137, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0))=k2_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_36]), c_0_35]), c_0_122])])).
% 9.93/10.09  cnf(c_0_138, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),k2_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_68]), c_0_84])])).
% 9.93/10.09  cnf(c_0_139, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_131])).
% 9.93/10.09  cnf(c_0_140, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_132, c_0_44])).
% 9.93/10.09  cnf(c_0_141, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)=k2_tops_1(esk2_0,esk3_0)|v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_76]), c_0_135])])).
% 9.93/10.09  cnf(c_0_142, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0))=k2_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_138])])).
% 9.93/10.09  fof(c_0_143, plain, ![X57, X58]:(~v2_pre_topc(X57)|~l1_pre_topc(X57)|~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|v3_pre_topc(k1_tops_1(X57,X58),X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 9.93/10.09  cnf(c_0_144, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_35]), c_0_36])])).
% 9.93/10.09  cnf(c_0_145, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_58, c_0_121])).
% 9.93/10.09  cnf(c_0_146, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0))=esk3_0|v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_76])])).
% 9.93/10.09  cnf(c_0_147, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0))=k1_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_142]), c_0_138])])).
% 9.93/10.09  cnf(c_0_148, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_143])).
% 9.93/10.09  cnf(c_0_149, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.93/10.09  cnf(c_0_150, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))|~v3_pre_topc(X1,esk2_0)|~r1_tarski(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_44]), c_0_145])).
% 9.93/10.09  cnf(c_0_151, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0|v3_pre_topc(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 9.93/10.09  cnf(c_0_152, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0|~r1_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_70, c_0_122])).
% 9.93/10.09  cnf(c_0_153, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)!=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.93/10.09  cnf(c_0_154, negated_conjecture, (v3_pre_topc(k1_tops_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_35]), c_0_149]), c_0_36])])).
% 9.93/10.09  cnf(c_0_155, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_151]), c_0_84])]), c_0_152])).
% 9.93/10.09  cnf(c_0_156, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)!=k2_tops_1(esk2_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_134]), c_0_76]), c_0_135])])).
% 9.93/10.09  cnf(c_0_157, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_154, c_0_155])).
% 9.93/10.09  cnf(c_0_158, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)!=k2_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_156, c_0_157])])).
% 9.93/10.09  cnf(c_0_159, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_142, c_0_155]), c_0_158]), ['proof']).
% 9.93/10.09  # SZS output end CNFRefutation
% 9.93/10.09  # Proof object total steps             : 160
% 9.93/10.09  # Proof object clause steps            : 103
% 9.93/10.09  # Proof object formula steps           : 57
% 9.93/10.09  # Proof object conjectures             : 47
% 9.93/10.09  # Proof object clause conjectures      : 44
% 9.93/10.09  # Proof object formula conjectures     : 3
% 9.93/10.09  # Proof object initial clauses used    : 34
% 9.93/10.09  # Proof object initial formulas used   : 28
% 9.93/10.09  # Proof object generating inferences   : 57
% 9.93/10.09  # Proof object simplifying inferences  : 64
% 9.93/10.09  # Training examples: 0 positive, 0 negative
% 9.93/10.09  # Parsed axioms                        : 31
% 9.93/10.09  # Removed by relevancy pruning/SinE    : 0
% 9.93/10.09  # Initial clauses                      : 38
% 9.93/10.09  # Removed in clause preprocessing      : 3
% 9.93/10.09  # Initial clauses in saturation        : 35
% 9.93/10.09  # Processed clauses                    : 62133
% 9.93/10.09  # ...of these trivial                  : 1899
% 9.93/10.09  # ...subsumed                          : 50901
% 9.93/10.09  # ...remaining for further processing  : 9332
% 9.93/10.09  # Other redundant clauses eliminated   : 2
% 9.93/10.09  # Clauses deleted for lack of memory   : 0
% 9.93/10.09  # Backward-subsumed                    : 671
% 9.93/10.09  # Backward-rewritten                   : 1881
% 9.93/10.09  # Generated clauses                    : 1158664
% 9.93/10.09  # ...of the previous two non-trivial   : 986059
% 9.93/10.09  # Contextual simplify-reflections      : 158
% 9.93/10.09  # Paramodulations                      : 1158653
% 9.93/10.09  # Factorizations                       : 0
% 9.93/10.09  # Equation resolutions                 : 2
% 9.93/10.09  # Propositional unsat checks           : 0
% 9.93/10.09  #    Propositional check models        : 0
% 9.93/10.09  #    Propositional check unsatisfiable : 0
% 9.93/10.09  #    Propositional clauses             : 0
% 9.93/10.09  #    Propositional clauses after purity: 0
% 9.93/10.09  #    Propositional unsat core size     : 0
% 9.93/10.09  #    Propositional preprocessing time  : 0.000
% 9.93/10.09  #    Propositional encoding time       : 0.000
% 9.93/10.09  #    Propositional solver time         : 0.000
% 9.93/10.09  #    Success case prop preproc time    : 0.000
% 9.93/10.09  #    Success case prop encoding time   : 0.000
% 9.93/10.09  #    Success case prop solver time     : 0.000
% 9.93/10.09  # Current number of processed clauses  : 6741
% 9.93/10.09  #    Positive orientable unit clauses  : 2067
% 9.93/10.09  #    Positive unorientable unit clauses: 14
% 9.93/10.09  #    Negative unit clauses             : 13
% 9.93/10.09  #    Non-unit-clauses                  : 4647
% 9.93/10.09  # Current number of unprocessed clauses: 917770
% 9.93/10.09  # ...number of literals in the above   : 2455043
% 9.93/10.09  # Current number of archived formulas  : 0
% 9.93/10.09  # Current number of archived clauses   : 2589
% 9.93/10.09  # Clause-clause subsumption calls (NU) : 4590211
% 9.93/10.09  # Rec. Clause-clause subsumption calls : 3497082
% 9.93/10.09  # Non-unit clause-clause subsumptions  : 33687
% 9.93/10.09  # Unit Clause-clause subsumption calls : 61747
% 9.93/10.09  # Rewrite failures with RHS unbound    : 0
% 9.93/10.09  # BW rewrite match attempts            : 58787
% 9.93/10.09  # BW rewrite match successes           : 232
% 9.93/10.09  # Condensation attempts                : 0
% 9.93/10.09  # Condensation successes               : 0
% 9.93/10.09  # Termbank termtop insertions          : 26208482
% 9.93/10.12  
% 9.93/10.12  # -------------------------------------------------
% 9.93/10.12  # User time                : 9.393 s
% 9.93/10.12  # System time              : 0.385 s
% 9.93/10.12  # Total time               : 9.777 s
% 9.93/10.12  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
