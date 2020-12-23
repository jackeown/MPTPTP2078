%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:17 EST 2020

% Result     : Theorem 39.02s
% Output     : CNFRefutation 39.02s
% Verified   : 
% Statistics : Number of formulae       :  177 (17584 expanded)
%              Number of clauses        :  126 (8316 expanded)
%              Number of leaves         :   25 (4619 expanded)
%              Depth                    :   20
%              Number of atoms          :  425 (23745 expanded)
%              Number of equality atoms :  138 (14732 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_25,plain,(
    ! [X25,X26] : k4_xboole_0(X25,X26) = k5_xboole_0(X25,k3_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_26,plain,(
    ! [X49,X50] : k1_setfam_1(k2_tarski(X49,X50)) = k3_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_27,plain,(
    ! [X30,X31] : r1_tarski(k4_xboole_0(X30,X31),X30) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X29] : k3_xboole_0(X29,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_31,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k3_xboole_0(X27,X28) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_32,plain,(
    ! [X33,X34] : k4_xboole_0(X33,k4_xboole_0(X33,X34)) = k3_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_33,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | k3_subset_1(X37,X38) = k4_xboole_0(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_34,plain,(
    ! [X51,X52] :
      ( ( ~ m1_subset_1(X51,k1_zfmisc_1(X52))
        | r1_tarski(X51,X52) )
      & ( ~ r1_tarski(X51,X52)
        | m1_subset_1(X51,k1_zfmisc_1(X52)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_37,plain,(
    ! [X32] : k4_xboole_0(X32,k1_xboole_0) = X32 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k4_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_46,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_29])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_29])).

fof(c_0_49,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | k7_subset_1(X46,X47,X48) = k4_xboole_0(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_50,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X44))
      | k3_subset_1(X44,k3_subset_1(X44,X45)) = X45 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_29]),c_0_36]),c_0_36])).

cnf(c_0_52,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_53,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_44,c_0_36])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_56,plain,(
    ! [X35,X36] : k2_tarski(X35,X36) = k2_tarski(X36,X35) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_60,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | m1_subset_1(k3_subset_1(X39,X40),k1_zfmisc_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_61,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_54,c_0_47])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_51])).

cnf(c_0_66,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_36])).

cnf(c_0_67,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_57,c_0_29])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_70,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_36])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_53])])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_47]),c_0_64])).

cnf(c_0_74,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_47])).

cnf(c_0_75,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_77,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_67])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(er,[status(thm)],[c_0_68])).

fof(c_0_79,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

cnf(c_0_80,plain,
    ( k3_subset_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_81,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_82,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_73])).

cnf(c_0_83,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_74])).

cnf(c_0_84,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_75,c_0_36])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_64])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_47]),c_0_64])).

cnf(c_0_87,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_78,c_0_48])).

fof(c_0_89,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) )
    & ( v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_79])])])).

cnf(c_0_90,plain,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_77]),c_0_82]),c_0_83])])).

cnf(c_0_91,plain,
    ( X1 = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | r2_hidden(esk2_3(X2,X3,X1),X2)
    | r2_hidden(esk2_3(X2,X3,X1),X1) ),
    inference(rw,[status(thm)],[c_0_84,c_0_72])).

cnf(c_0_92,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_77]),c_0_85])).

cnf(c_0_93,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_86]),c_0_47]),c_0_64])).

cnf(c_0_94,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_48]),c_0_73])])).

cnf(c_0_95,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_96,plain,(
    ! [X23,X24] :
      ( ( r1_tarski(X23,X24)
        | X23 != X24 )
      & ( r1_tarski(X24,X23)
        | X23 != X24 )
      & ( ~ r1_tarski(X23,X24)
        | ~ r1_tarski(X24,X23)
        | X23 = X24 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_97,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_87,c_0_36])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_88,c_0_59])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_100,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_90]),c_0_90]),c_0_90]),c_0_92])).

cnf(c_0_101,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_47]),c_0_64]),c_0_83])])).

cnf(c_0_102,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_51])).

cnf(c_0_103,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_91])).

cnf(c_0_104,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_93]),c_0_94]),c_0_82])])).

cnf(c_0_105,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_95,c_0_36])).

cnf(c_0_106,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

fof(c_0_107,plain,(
    ! [X59,X60,X61] :
      ( ~ l1_pre_topc(X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))
      | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X59)))
      | ~ v3_pre_topc(X60,X59)
      | ~ r1_tarski(X60,X61)
      | r1_tarski(X60,k1_tops_1(X59,X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

fof(c_0_108,plain,(
    ! [X66,X67] :
      ( ~ l1_pre_topc(X66)
      | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))
      | k1_tops_1(X66,X67) = k7_subset_1(u1_struct_0(X66),X67,k2_tops_1(X66,X67)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_109,plain,
    ( r1_tarski(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_43,c_0_72])).

cnf(c_0_110,plain,
    ( X1 = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk2_3(X2,X3,X1),X3) ),
    inference(rw,[status(thm)],[c_0_97,c_0_72])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_112,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_67])).

cnf(c_0_113,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_100]),c_0_101]),c_0_102])])).

cnf(c_0_114,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_103]),c_0_104]),c_0_102])])).

cnf(c_0_115,plain,
    ( X1 = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | r2_hidden(esk2_3(X2,X3,X1),X3)
    | ~ r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk2_3(X2,X3,X1),X2) ),
    inference(rw,[status(thm)],[c_0_105,c_0_72])).

cnf(c_0_116,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_106,c_0_59])).

cnf(c_0_117,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_118,plain,
    ( m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_81]),c_0_102])])).

cnf(c_0_119,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

fof(c_0_120,plain,(
    ! [X62,X63] :
      ( ~ l1_pre_topc(X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))
      | k2_tops_1(X62,X63) = k2_tops_1(X62,k3_subset_1(u1_struct_0(X62),X63)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

cnf(c_0_121,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_72])).

cnf(c_0_122,plain,
    ( r1_tarski(k3_subset_1(X1,k1_setfam_1(k2_tarski(X2,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_67])).

cnf(c_0_123,negated_conjecture,
    ( X1 = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,u1_struct_0(esk3_0))))
    | r2_hidden(esk2_3(X2,u1_struct_0(esk3_0),X1),X1)
    | ~ r2_hidden(esk2_3(X2,u1_struct_0(esk3_0),X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_124,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_125,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | r2_hidden(esk2_3(X2,X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_114,c_0_67])).

cnf(c_0_126,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_103]),c_0_103])).

fof(c_0_127,plain,(
    ! [X57,X58] :
      ( ~ l1_pre_topc(X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
      | k2_tops_1(X57,X58) = k7_subset_1(u1_struct_0(X57),k2_pre_topc(X57,X58),k1_tops_1(X57,X58)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_128,plain,
    ( X1 = k1_tops_1(X2,X3)
    | ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k1_tops_1(X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_129,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

fof(c_0_130,plain,(
    ! [X64,X65] :
      ( ~ l1_pre_topc(X64)
      | ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))
      | k2_pre_topc(X64,X65) = k4_subset_1(u1_struct_0(X64),X65,k2_tops_1(X64,X65)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_131,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_132,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X2,X1)))) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_67])).

cnf(c_0_133,plain,
    ( m1_subset_1(k3_subset_1(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_122])).

cnf(c_0_134,negated_conjecture,
    ( k3_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) = k1_xboole_0
    | r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_92])).

cnf(c_0_135,plain,
    ( ~ r2_hidden(X1,k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_76,c_0_72])).

cnf(c_0_136,plain,
    ( k7_subset_1(X1,X2,X3) = X2
    | r2_hidden(esk2_3(X3,X2,X3),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_125]),c_0_101])).

cnf(c_0_137,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,k1_setfam_1(k2_tarski(X3,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_67])).

cnf(c_0_138,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_126]),c_0_104]),c_0_102])])).

cnf(c_0_139,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_127])).

cnf(c_0_140,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_73])])).

cnf(c_0_141,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_142,plain,
    ( k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),k1_setfam_1(k2_tarski(X2,u1_struct_0(X1))))) = k2_tops_1(X1,k1_setfam_1(k2_tarski(X2,u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_133])])).

cnf(c_0_143,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) = esk4_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_134]),c_0_101]),c_0_102])]),c_0_48])).

cnf(c_0_144,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

fof(c_0_145,plain,(
    ! [X53,X54] :
      ( ~ l1_pre_topc(X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
      | m1_subset_1(k2_tops_1(X53,X54),k1_zfmisc_1(u1_struct_0(X53))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_146,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k7_subset_1(X2,X1,X4))
    | ~ r2_hidden(X3,X4) ),
    inference(spm,[status(thm)],[c_0_135,c_0_81])).

cnf(c_0_147,plain,
    ( k7_subset_1(X1,X1,X2) = X1
    | r2_hidden(esk2_3(X2,X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_136,c_0_82])).

cnf(c_0_148,plain,
    ( k7_subset_1(X1,X2,X3) = X2
    | r2_hidden(esk2_3(X3,X2,X3),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_101])).

cnf(c_0_149,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_150,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) = k2_tops_1(X1,X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

fof(c_0_151,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | ~ m1_subset_1(X43,k1_zfmisc_1(X41))
      | m1_subset_1(k4_subset_1(X41,X42,X43),k1_zfmisc_1(X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_152,plain,
    ( k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2)) = k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_131]),c_0_70])).

cnf(c_0_153,negated_conjecture,
    ( k2_tops_1(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0)) = k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_144])])).

cnf(c_0_154,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_132,c_0_143])).

cnf(c_0_155,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_143])).

cnf(c_0_156,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_145])).

cnf(c_0_157,plain,
    ( k7_subset_1(X1,X1,k7_subset_1(X2,X3,X4)) = X1
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(esk2_3(k7_subset_1(X2,X3,X4),X1,k7_subset_1(X2,X3,X4)),X4) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_158,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) = esk4_0
    | r2_hidden(esk2_3(X1,esk4_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_148,c_0_99])).

cnf(c_0_159,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_160,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_144]),c_0_99])])).

cnf(c_0_161,plain,
    ( k7_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2)) = k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_131]),c_0_70])).

cnf(c_0_162,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_151])).

cnf(c_0_163,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k2_pre_topc(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_154]),c_0_154]),c_0_144]),c_0_155])])).

cnf(c_0_164,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_153]),c_0_144]),c_0_155])])).

cnf(c_0_165,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_81])).

cnf(c_0_166,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(X1,X2,esk4_0)) = esk4_0
    | k7_subset_1(esk4_0,esk4_0,k7_subset_1(X1,X2,esk4_0)) = esk4_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_157,c_0_158])).

cnf(c_0_167,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_159,c_0_160])).

cnf(c_0_168,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_153]),c_0_154]),c_0_154]),c_0_144]),c_0_155])])).

cnf(c_0_169,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_163]),c_0_164]),c_0_99])])).

fof(c_0_170,plain,(
    ! [X55,X56] :
      ( ~ v2_pre_topc(X55)
      | ~ l1_pre_topc(X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
      | v3_pre_topc(k1_tops_1(X55,X56),X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_171,plain,
    ( k7_subset_1(X1,X2,k2_tops_1(X3,X2)) = k1_tops_1(X3,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_165])).

cnf(c_0_172,negated_conjecture,
    ( k7_subset_1(esk4_0,esk4_0,k2_tops_1(esk3_0,esk4_0)) = esk4_0
    | k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_167]),c_0_168]),c_0_169])])).

cnf(c_0_173,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_170])).

cnf(c_0_174,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_172]),c_0_144]),c_0_99]),c_0_82])])).

cnf(c_0_175,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_176,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_174]),c_0_175]),c_0_144]),c_0_99])]),c_0_160]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 39.02/39.21  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 39.02/39.21  # and selection function SelectMaxLComplexAvoidPosPred.
% 39.02/39.21  #
% 39.02/39.21  # Preprocessing time       : 0.029 s
% 39.02/39.21  
% 39.02/39.21  # Proof found!
% 39.02/39.21  # SZS status Theorem
% 39.02/39.21  # SZS output start CNFRefutation
% 39.02/39.21  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 39.02/39.21  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 39.02/39.21  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 39.02/39.21  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 39.02/39.21  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 39.02/39.21  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 39.02/39.21  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 39.02/39.21  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 39.02/39.21  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 39.02/39.21  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 39.02/39.21  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 39.02/39.21  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 39.02/39.21  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 39.02/39.21  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 39.02/39.21  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 39.02/39.21  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 39.02/39.21  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 39.02/39.21  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 39.02/39.21  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 39.02/39.21  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 39.02/39.21  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 39.02/39.21  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 39.02/39.21  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 39.02/39.21  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 39.02/39.21  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 39.02/39.21  fof(c_0_25, plain, ![X25, X26]:k4_xboole_0(X25,X26)=k5_xboole_0(X25,k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 39.02/39.21  fof(c_0_26, plain, ![X49, X50]:k1_setfam_1(k2_tarski(X49,X50))=k3_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 39.02/39.21  fof(c_0_27, plain, ![X30, X31]:r1_tarski(k4_xboole_0(X30,X31),X30), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 39.02/39.21  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 39.02/39.21  cnf(c_0_29, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 39.02/39.21  fof(c_0_30, plain, ![X29]:k3_xboole_0(X29,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 39.02/39.21  fof(c_0_31, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k3_xboole_0(X27,X28)=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 39.02/39.21  fof(c_0_32, plain, ![X33, X34]:k4_xboole_0(X33,k4_xboole_0(X33,X34))=k3_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 39.02/39.21  fof(c_0_33, plain, ![X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|k3_subset_1(X37,X38)=k4_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 39.02/39.21  fof(c_0_34, plain, ![X51, X52]:((~m1_subset_1(X51,k1_zfmisc_1(X52))|r1_tarski(X51,X52))&(~r1_tarski(X51,X52)|m1_subset_1(X51,k1_zfmisc_1(X52)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 39.02/39.21  cnf(c_0_35, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 39.02/39.21  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 39.02/39.21  fof(c_0_37, plain, ![X32]:k4_xboole_0(X32,k1_xboole_0)=X32, inference(variable_rename,[status(thm)],[t3_boole])).
% 39.02/39.21  cnf(c_0_38, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 39.02/39.21  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 39.02/39.21  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 39.02/39.21  cnf(c_0_41, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 39.02/39.21  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 39.02/39.21  cnf(c_0_43, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 39.02/39.21  cnf(c_0_44, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 39.02/39.21  fof(c_0_45, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k4_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k4_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))&(~r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 39.02/39.21  fof(c_0_46, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 39.02/39.21  cnf(c_0_47, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_38, c_0_29])).
% 39.02/39.21  cnf(c_0_48, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_29])).
% 39.02/39.21  fof(c_0_49, plain, ![X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|k7_subset_1(X46,X47,X48)=k4_xboole_0(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 39.02/39.21  fof(c_0_50, plain, ![X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(X44))|k3_subset_1(X44,k3_subset_1(X44,X45))=X45), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 39.02/39.21  cnf(c_0_51, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_29]), c_0_36]), c_0_36])).
% 39.02/39.21  cnf(c_0_52, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_41, c_0_36])).
% 39.02/39.21  cnf(c_0_53, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 39.02/39.21  cnf(c_0_54, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_44, c_0_36])).
% 39.02/39.21  cnf(c_0_55, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 39.02/39.21  fof(c_0_56, plain, ![X35, X36]:k2_tarski(X35,X36)=k2_tarski(X36,X35), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 39.02/39.21  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 39.02/39.21  cnf(c_0_58, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 39.02/39.21  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 39.02/39.21  fof(c_0_60, plain, ![X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|m1_subset_1(k3_subset_1(X39,X40),k1_zfmisc_1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 39.02/39.21  cnf(c_0_61, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 39.02/39.21  cnf(c_0_62, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 39.02/39.21  cnf(c_0_63, plain, (k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 39.02/39.21  cnf(c_0_64, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_54, c_0_47])).
% 39.02/39.21  cnf(c_0_65, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_43, c_0_51])).
% 39.02/39.21  cnf(c_0_66, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_55, c_0_36])).
% 39.02/39.21  cnf(c_0_67, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 39.02/39.21  cnf(c_0_68, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_57, c_0_29])).
% 39.02/39.21  cnf(c_0_69, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 39.02/39.21  cnf(c_0_70, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 39.02/39.21  cnf(c_0_71, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_61, c_0_36])).
% 39.02/39.21  cnf(c_0_72, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_53])])).
% 39.02/39.21  cnf(c_0_73, plain, (r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_47]), c_0_64])).
% 39.02/39.21  cnf(c_0_74, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_65, c_0_47])).
% 39.02/39.21  cnf(c_0_75, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 39.02/39.21  cnf(c_0_76, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_66])).
% 39.02/39.21  cnf(c_0_77, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_67])).
% 39.02/39.21  cnf(c_0_78, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2)))), inference(er,[status(thm)],[c_0_68])).
% 39.02/39.21  fof(c_0_79, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 39.02/39.21  cnf(c_0_80, plain, (k3_subset_1(k1_xboole_0,X1)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 39.02/39.21  cnf(c_0_81, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_71, c_0_72])).
% 39.02/39.21  cnf(c_0_82, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_73])).
% 39.02/39.21  cnf(c_0_83, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_74])).
% 39.02/39.21  cnf(c_0_84, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_75, c_0_36])).
% 39.02/39.21  cnf(c_0_85, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_64])).
% 39.02/39.21  cnf(c_0_86, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_47]), c_0_64])).
% 39.02/39.21  cnf(c_0_87, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 39.02/39.21  cnf(c_0_88, plain, (r2_hidden(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_78, c_0_48])).
% 39.02/39.21  fof(c_0_89, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))&(v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_79])])])).
% 39.02/39.21  cnf(c_0_90, plain, (k7_subset_1(X1,k1_xboole_0,X2)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_77]), c_0_82]), c_0_83])])).
% 39.02/39.21  cnf(c_0_91, plain, (X1=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))|r2_hidden(esk2_3(X2,X3,X1),X2)|r2_hidden(esk2_3(X2,X3,X1),X1)), inference(rw,[status(thm)],[c_0_84, c_0_72])).
% 39.02/39.21  cnf(c_0_92, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_77]), c_0_85])).
% 39.02/39.21  cnf(c_0_93, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_86]), c_0_47]), c_0_64])).
% 39.02/39.21  cnf(c_0_94, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_48]), c_0_73])])).
% 39.02/39.21  cnf(c_0_95, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 39.02/39.21  fof(c_0_96, plain, ![X23, X24]:(((r1_tarski(X23,X24)|X23!=X24)&(r1_tarski(X24,X23)|X23!=X24))&(~r1_tarski(X23,X24)|~r1_tarski(X24,X23)|X23=X24)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 39.02/39.21  cnf(c_0_97, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_87, c_0_36])).
% 39.02/39.21  cnf(c_0_98, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_88, c_0_59])).
% 39.02/39.21  cnf(c_0_99, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 39.02/39.21  cnf(c_0_100, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_90]), c_0_90]), c_0_90]), c_0_92])).
% 39.02/39.21  cnf(c_0_101, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_47]), c_0_64]), c_0_83])])).
% 39.02/39.21  cnf(c_0_102, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_51])).
% 39.02/39.21  cnf(c_0_103, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_91])).
% 39.02/39.21  cnf(c_0_104, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_93]), c_0_94]), c_0_82])])).
% 39.02/39.21  cnf(c_0_105, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_95, c_0_36])).
% 39.02/39.21  cnf(c_0_106, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 39.02/39.21  fof(c_0_107, plain, ![X59, X60, X61]:(~l1_pre_topc(X59)|(~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X59)))|(~v3_pre_topc(X60,X59)|~r1_tarski(X60,X61)|r1_tarski(X60,k1_tops_1(X59,X61)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 39.02/39.21  fof(c_0_108, plain, ![X66, X67]:(~l1_pre_topc(X66)|(~m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))|k1_tops_1(X66,X67)=k7_subset_1(u1_struct_0(X66),X67,k2_tops_1(X66,X67)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 39.02/39.21  cnf(c_0_109, plain, (r1_tarski(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_43, c_0_72])).
% 39.02/39.21  cnf(c_0_110, plain, (X1=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))|r2_hidden(esk2_3(X2,X3,X1),X1)|~r2_hidden(esk2_3(X2,X3,X1),X3)), inference(rw,[status(thm)],[c_0_97, c_0_72])).
% 39.02/39.21  cnf(c_0_111, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 39.02/39.21  cnf(c_0_112, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_65, c_0_67])).
% 39.02/39.21  cnf(c_0_113, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_100]), c_0_101]), c_0_102])])).
% 39.02/39.21  cnf(c_0_114, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_103]), c_0_104]), c_0_102])])).
% 39.02/39.21  cnf(c_0_115, plain, (X1=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))|r2_hidden(esk2_3(X2,X3,X1),X3)|~r2_hidden(esk2_3(X2,X3,X1),X1)|~r2_hidden(esk2_3(X2,X3,X1),X2)), inference(rw,[status(thm)],[c_0_105, c_0_72])).
% 39.02/39.21  cnf(c_0_116, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_106, c_0_59])).
% 39.02/39.21  cnf(c_0_117, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 39.02/39.21  cnf(c_0_118, plain, (m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_81]), c_0_102])])).
% 39.02/39.21  cnf(c_0_119, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_108])).
% 39.02/39.21  fof(c_0_120, plain, ![X62, X63]:(~l1_pre_topc(X62)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))|k2_tops_1(X62,X63)=k2_tops_1(X62,k3_subset_1(u1_struct_0(X62),X63)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 39.02/39.21  cnf(c_0_121, plain, (k3_subset_1(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_63, c_0_72])).
% 39.02/39.21  cnf(c_0_122, plain, (r1_tarski(k3_subset_1(X1,k1_setfam_1(k2_tarski(X2,X1))),X1)), inference(spm,[status(thm)],[c_0_109, c_0_67])).
% 39.02/39.21  cnf(c_0_123, negated_conjecture, (X1=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,u1_struct_0(esk3_0))))|r2_hidden(esk2_3(X2,u1_struct_0(esk3_0),X1),X1)|~r2_hidden(esk2_3(X2,u1_struct_0(esk3_0),X1),esk4_0)), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 39.02/39.21  cnf(c_0_124, plain, (r1_tarski(X1,X2)|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 39.02/39.21  cnf(c_0_125, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|r2_hidden(esk2_3(X2,X1,X2),X2)), inference(spm,[status(thm)],[c_0_114, c_0_67])).
% 39.02/39.21  cnf(c_0_126, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1|r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_103]), c_0_103])).
% 39.02/39.21  fof(c_0_127, plain, ![X57, X58]:(~l1_pre_topc(X57)|(~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|k2_tops_1(X57,X58)=k7_subset_1(u1_struct_0(X57),k2_pre_topc(X57,X58),k1_tops_1(X57,X58)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 39.02/39.21  cnf(c_0_128, plain, (X1=k1_tops_1(X2,X3)|~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(k1_tops_1(X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 39.02/39.21  cnf(c_0_129, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 39.02/39.21  fof(c_0_130, plain, ![X64, X65]:(~l1_pre_topc(X64)|(~m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))|k2_pre_topc(X64,X65)=k4_subset_1(u1_struct_0(X64),X65,k2_tops_1(X64,X65)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 39.02/39.21  cnf(c_0_131, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_120])).
% 39.02/39.21  cnf(c_0_132, plain, (k3_subset_1(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X2,X1))))=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_121, c_0_67])).
% 39.02/39.21  cnf(c_0_133, plain, (m1_subset_1(k3_subset_1(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_122])).
% 39.02/39.21  cnf(c_0_134, negated_conjecture, (k3_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))=k1_xboole_0|r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_92])).
% 39.02/39.21  cnf(c_0_135, plain, (~r2_hidden(X1,k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3))))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_76, c_0_72])).
% 39.02/39.21  cnf(c_0_136, plain, (k7_subset_1(X1,X2,X3)=X2|r2_hidden(esk2_3(X3,X2,X3),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_125]), c_0_101])).
% 39.02/39.21  cnf(c_0_137, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,k1_setfam_1(k2_tarski(X3,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_81, c_0_67])).
% 39.02/39.21  cnf(c_0_138, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|r2_hidden(esk2_3(X1,X2,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_126]), c_0_104]), c_0_102])])).
% 39.02/39.21  cnf(c_0_139, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_127])).
% 39.02/39.21  cnf(c_0_140, plain, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_73])])).
% 39.02/39.21  cnf(c_0_141, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_130])).
% 39.02/39.21  cnf(c_0_142, plain, (k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),k1_setfam_1(k2_tarski(X2,u1_struct_0(X1)))))=k2_tops_1(X1,k1_setfam_1(k2_tarski(X2,u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_133])])).
% 39.02/39.21  cnf(c_0_143, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))=esk4_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_134]), c_0_101]), c_0_102])]), c_0_48])).
% 39.02/39.21  cnf(c_0_144, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 39.02/39.21  fof(c_0_145, plain, ![X53, X54]:(~l1_pre_topc(X53)|~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))|m1_subset_1(k2_tops_1(X53,X54),k1_zfmisc_1(u1_struct_0(X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 39.02/39.21  cnf(c_0_146, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k7_subset_1(X2,X1,X4))|~r2_hidden(X3,X4)), inference(spm,[status(thm)],[c_0_135, c_0_81])).
% 39.02/39.21  cnf(c_0_147, plain, (k7_subset_1(X1,X1,X2)=X1|r2_hidden(esk2_3(X2,X1,X2),X2)), inference(spm,[status(thm)],[c_0_136, c_0_82])).
% 39.02/39.21  cnf(c_0_148, plain, (k7_subset_1(X1,X2,X3)=X2|r2_hidden(esk2_3(X3,X2,X3),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_101])).
% 39.02/39.21  cnf(c_0_149, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 39.02/39.21  cnf(c_0_150, plain, (k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)=k2_tops_1(X1,X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 39.02/39.21  fof(c_0_151, plain, ![X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|~m1_subset_1(X43,k1_zfmisc_1(X41))|m1_subset_1(k4_subset_1(X41,X42,X43),k1_zfmisc_1(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 39.02/39.21  cnf(c_0_152, plain, (k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2))=k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_131]), c_0_70])).
% 39.02/39.21  cnf(c_0_153, negated_conjecture, (k2_tops_1(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0))=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_144])])).
% 39.02/39.21  cnf(c_0_154, negated_conjecture, (k3_subset_1(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_132, c_0_143])).
% 39.02/39.21  cnf(c_0_155, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_133, c_0_143])).
% 39.02/39.21  cnf(c_0_156, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_145])).
% 39.02/39.21  cnf(c_0_157, plain, (k7_subset_1(X1,X1,k7_subset_1(X2,X3,X4))=X1|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(esk2_3(k7_subset_1(X2,X3,X4),X1,k7_subset_1(X2,X3,X4)),X4)), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 39.02/39.21  cnf(c_0_158, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)=esk4_0|r2_hidden(esk2_3(X1,esk4_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_148, c_0_99])).
% 39.02/39.21  cnf(c_0_159, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 39.02/39.21  cnf(c_0_160, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_144]), c_0_99])])).
% 39.02/39.21  cnf(c_0_161, plain, (k7_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2))=k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_131]), c_0_70])).
% 39.02/39.21  cnf(c_0_162, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_151])).
% 39.02/39.21  cnf(c_0_163, negated_conjecture, (k4_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k2_pre_topc(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_154]), c_0_154]), c_0_144]), c_0_155])])).
% 39.02/39.21  cnf(c_0_164, negated_conjecture, (m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_153]), c_0_144]), c_0_155])])).
% 39.02/39.21  cnf(c_0_165, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_81, c_0_81])).
% 39.02/39.21  cnf(c_0_166, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(X1,X2,esk4_0))=esk4_0|k7_subset_1(esk4_0,esk4_0,k7_subset_1(X1,X2,esk4_0))=esk4_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_157, c_0_158])).
% 39.02/39.22  cnf(c_0_167, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[c_0_159, c_0_160])).
% 39.02/39.22  cnf(c_0_168, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_153]), c_0_154]), c_0_154]), c_0_144]), c_0_155])])).
% 39.02/39.22  cnf(c_0_169, negated_conjecture, (m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_163]), c_0_164]), c_0_99])])).
% 39.02/39.22  fof(c_0_170, plain, ![X55, X56]:(~v2_pre_topc(X55)|~l1_pre_topc(X55)|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|v3_pre_topc(k1_tops_1(X55,X56),X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 39.02/39.22  cnf(c_0_171, plain, (k7_subset_1(X1,X2,k2_tops_1(X3,X2))=k1_tops_1(X3,X2)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_119, c_0_165])).
% 39.02/39.22  cnf(c_0_172, negated_conjecture, (k7_subset_1(esk4_0,esk4_0,k2_tops_1(esk3_0,esk4_0))=esk4_0|k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_167]), c_0_168]), c_0_169])])).
% 39.02/39.22  cnf(c_0_173, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_170])).
% 39.02/39.22  cnf(c_0_174, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_172]), c_0_144]), c_0_99]), c_0_82])])).
% 39.02/39.22  cnf(c_0_175, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 39.02/39.22  cnf(c_0_176, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_174]), c_0_175]), c_0_144]), c_0_99])]), c_0_160]), ['proof']).
% 39.02/39.22  # SZS output end CNFRefutation
% 39.02/39.22  # Proof object total steps             : 177
% 39.02/39.22  # Proof object clause steps            : 126
% 39.02/39.22  # Proof object formula steps           : 51
% 39.02/39.22  # Proof object conjectures             : 26
% 39.02/39.22  # Proof object clause conjectures      : 23
% 39.02/39.22  # Proof object formula conjectures     : 3
% 39.02/39.22  # Proof object initial clauses used    : 33
% 39.02/39.22  # Proof object initial formulas used   : 25
% 39.02/39.22  # Proof object generating inferences   : 69
% 39.02/39.22  # Proof object simplifying inferences  : 110
% 39.02/39.22  # Training examples: 0 positive, 0 negative
% 39.02/39.22  # Parsed axioms                        : 25
% 39.02/39.22  # Removed by relevancy pruning/SinE    : 0
% 39.02/39.22  # Initial clauses                      : 42
% 39.02/39.22  # Removed in clause preprocessing      : 2
% 39.02/39.22  # Initial clauses in saturation        : 40
% 39.02/39.22  # Processed clauses                    : 69574
% 39.02/39.22  # ...of these trivial                  : 484
% 39.02/39.22  # ...subsumed                          : 61285
% 39.02/39.22  # ...remaining for further processing  : 7805
% 39.02/39.22  # Other redundant clauses eliminated   : 32
% 39.02/39.22  # Clauses deleted for lack of memory   : 264689
% 39.02/39.22  # Backward-subsumed                    : 925
% 39.02/39.22  # Backward-rewritten                   : 620
% 39.02/39.22  # Generated clauses                    : 3387988
% 39.02/39.22  # ...of the previous two non-trivial   : 3088606
% 39.02/39.22  # Contextual simplify-reflections      : 318
% 39.02/39.22  # Paramodulations                      : 3387140
% 39.02/39.22  # Factorizations                       : 814
% 39.02/39.22  # Equation resolutions                 : 32
% 39.02/39.22  # Propositional unsat checks           : 0
% 39.02/39.22  #    Propositional check models        : 0
% 39.02/39.22  #    Propositional check unsatisfiable : 0
% 39.02/39.22  #    Propositional clauses             : 0
% 39.02/39.22  #    Propositional clauses after purity: 0
% 39.02/39.22  #    Propositional unsat core size     : 0
% 39.02/39.22  #    Propositional preprocessing time  : 0.000
% 39.02/39.22  #    Propositional encoding time       : 0.000
% 39.02/39.22  #    Propositional solver time         : 0.000
% 39.02/39.22  #    Success case prop preproc time    : 0.000
% 39.02/39.22  #    Success case prop encoding time   : 0.000
% 39.02/39.22  #    Success case prop solver time     : 0.000
% 39.02/39.22  # Current number of processed clauses  : 6250
% 39.02/39.22  #    Positive orientable unit clauses  : 151
% 39.02/39.22  #    Positive unorientable unit clauses: 1
% 39.02/39.22  #    Negative unit clauses             : 10
% 39.02/39.22  #    Non-unit-clauses                  : 6088
% 39.02/39.22  # Current number of unprocessed clauses: 1856455
% 39.02/39.22  # ...number of literals in the above   : 7698674
% 39.02/39.22  # Current number of archived formulas  : 0
% 39.02/39.22  # Current number of archived clauses   : 1549
% 39.02/39.22  # Clause-clause subsumption calls (NU) : 4301333
% 39.02/39.22  # Rec. Clause-clause subsumption calls : 2347733
% 39.02/39.22  # Non-unit clause-clause subsumptions  : 50836
% 39.02/39.22  # Unit Clause-clause subsumption calls : 13844
% 39.02/39.22  # Rewrite failures with RHS unbound    : 0
% 39.02/39.22  # BW rewrite match attempts            : 404
% 39.02/39.22  # BW rewrite match successes           : 87
% 39.02/39.22  # Condensation attempts                : 0
% 39.02/39.22  # Condensation successes               : 0
% 39.02/39.22  # Termbank termtop insertions          : 71612464
% 39.09/39.29  
% 39.09/39.29  # -------------------------------------------------
% 39.09/39.29  # User time                : 38.048 s
% 39.09/39.29  # System time              : 0.896 s
% 39.09/39.29  # Total time               : 38.944 s
% 39.09/39.29  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
