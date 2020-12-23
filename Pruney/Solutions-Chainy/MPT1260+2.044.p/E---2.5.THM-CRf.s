%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:21 EST 2020

% Result     : Theorem 16.84s
% Output     : CNFRefutation 16.84s
% Verified   : 
% Statistics : Number of formulae       :  171 (1972 expanded)
%              Number of clauses        :  118 ( 856 expanded)
%              Number of leaves         :   26 ( 493 expanded)
%              Depth                    :   17
%              Number of atoms          :  321 (5214 expanded)
%              Number of equality atoms :   88 (1422 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

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

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_26,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

fof(c_0_28,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,k2_xboole_0(X15,X16))
      | r1_tarski(k4_xboole_0(X14,X15),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X28] : m1_subset_1(k2_subset_1(X28),k1_zfmisc_1(X28)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_31,plain,(
    ! [X25] : k2_subset_1(X25) = X25 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_32,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k9_subset_1(X22,X23,X24) = k9_subset_1(X22,X24,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

fof(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_34,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X42))
      | k9_subset_1(X42,X43,X44) = k3_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_35,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_36,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_39,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | k3_subset_1(X26,X27) = k4_xboole_0(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_40,plain,(
    ! [X48] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X48)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_41,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X31))
      | m1_subset_1(k9_subset_1(X31,X32,X33),k1_zfmisc_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_44,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_48,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_49,plain,(
    ! [X11,X12] : r1_tarski(k4_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_50,plain,(
    ! [X49,X50] :
      ( ( ~ m1_subset_1(X49,k1_zfmisc_1(X50))
        | r1_tarski(X49,X50) )
      & ( ~ r1_tarski(X49,X50)
        | m1_subset_1(X49,k1_zfmisc_1(X50)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_51,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(k4_xboole_0(X17,X18),X19)
      | r1_tarski(X17,k2_xboole_0(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_52,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_54,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_55,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | k3_subset_1(X37,k3_subset_1(X37,X38)) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_56,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_57,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_59,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_61,plain,
    ( k9_subset_1(X2,X3,X1) = k4_xboole_0(X3,k4_xboole_0(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_69,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_70,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_53])).

cnf(c_0_71,plain,
    ( k3_subset_1(X1,X1) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_58])).

fof(c_0_72,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | k7_subset_1(X39,X40,X41) = k4_xboole_0(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_45])])).

cnf(c_0_74,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) = k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_45])).

cnf(c_0_75,plain,
    ( k9_subset_1(X1,X2,X1) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_58])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_77,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X29))
      | m1_subset_1(k3_subset_1(X29,X30),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_78,plain,
    ( k9_subset_1(X1,X1,X2) = k9_subset_1(X1,X2,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_58])).

cnf(c_0_79,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_57])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,X2) = X3
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_81,plain,
    ( r1_tarski(k2_xboole_0(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_57]),c_0_70]),c_0_71])).

fof(c_0_83,plain,(
    ! [X67,X68] :
      ( ~ l1_pre_topc(X67)
      | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))
      | k1_tops_1(X67,X68) = k7_subset_1(u1_struct_0(X67),X68,k2_tops_1(X67,X68)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_84,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_85,plain,(
    ! [X54,X55] :
      ( ~ l1_pre_topc(X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
      | m1_subset_1(k2_pre_topc(X54,X55),k1_zfmisc_1(u1_struct_0(X54))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_60])).

cnf(c_0_87,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) = k9_subset_1(esk2_0,X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_88,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_89,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_63])).

cnf(c_0_90,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_91,plain,
    ( m1_subset_1(k9_subset_1(X1,X1,X2),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_78]),c_0_58])])).

cnf(c_0_92,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_79])).

cnf(c_0_93,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_63])).

cnf(c_0_94,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_79])])).

cnf(c_0_95,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_96,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_97,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_45])).

cnf(c_0_98,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(k9_subset_1(esk2_0,X1,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_100,plain,
    ( k9_subset_1(X1,X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_88])).

cnf(c_0_101,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X3),X4),X1),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_89])).

cnf(c_0_102,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_90])).

cnf(c_0_103,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_88])).

cnf(c_0_104,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_78])).

cnf(c_0_105,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_106,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_45]),c_0_96])]),c_0_97])).

cnf(c_0_107,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3) = k4_xboole_0(k2_pre_topc(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_98])).

fof(c_0_108,plain,(
    ! [X56,X57] :
      ( ~ l1_pre_topc(X56)
      | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
      | r1_tarski(X57,k2_pre_topc(X56,X57)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

fof(c_0_109,plain,(
    ! [X60,X61] :
      ( ~ l1_pre_topc(X60)
      | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))
      | k2_tops_1(X60,X61) = k7_subset_1(u1_struct_0(X60),k2_pre_topc(X60,X61),k1_tops_1(X60,X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_37])])).

cnf(c_0_111,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_101]),c_0_94])).

cnf(c_0_112,plain,
    ( k3_subset_1(X1,X2) = k4_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_88])).

cnf(c_0_113,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_88])).

cnf(c_0_114,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_88])).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(k9_subset_1(esk2_0,esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_103]),c_0_37])])).

cnf(c_0_116,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_117,plain,
    ( m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_100]),c_0_37])])).

cnf(c_0_118,negated_conjecture,
    ( k4_xboole_0(k1_tops_1(esk1_0,esk2_0),esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_119,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_120,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),X1) = k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_45]),c_0_96])])).

cnf(c_0_121,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_122,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

fof(c_0_123,plain,(
    ! [X62,X63,X64] :
      ( ~ l1_pre_topc(X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X62)))
      | ~ v3_pre_topc(X63,X62)
      | ~ r1_tarski(X63,X64)
      | r1_tarski(X63,k1_tops_1(X62,X64)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(k4_xboole_0(esk2_0,X1),X2),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_53])).

cnf(c_0_125,plain,
    ( k4_xboole_0(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114])).

cnf(c_0_126,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,esk2_0,X1),X2) = k4_xboole_0(k9_subset_1(esk2_0,esk2_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_115])).

cnf(c_0_127,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_58])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_53])).

cnf(c_0_129,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_68])).

cnf(c_0_130,plain,
    ( k3_subset_1(X1,k4_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_112])).

cnf(c_0_131,negated_conjecture,
    ( k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_132,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_45]),c_0_96])])).

cnf(c_0_133,negated_conjecture,
    ( k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_120]),c_0_96]),c_0_45])])).

cnf(c_0_134,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_136,negated_conjecture,
    ( k4_xboole_0(k9_subset_1(esk2_0,esk2_0,X1),k2_tops_1(esk1_0,k9_subset_1(esk2_0,esk2_0,X1))) = k1_tops_1(esk1_0,k9_subset_1(esk2_0,esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_115]),c_0_96])]),c_0_126])).

cnf(c_0_137,plain,
    ( r1_tarski(k9_subset_1(X1,X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_127,c_0_78])).

cnf(c_0_138,negated_conjecture,
    ( k9_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_118]),c_0_53]),c_0_78])).

cnf(c_0_139,negated_conjecture,
    ( k9_subset_1(esk2_0,X1,k1_tops_1(esk1_0,esk2_0)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_tops_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_128])).

cnf(c_0_140,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_129])).

cnf(c_0_141,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_132])])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_133])).

cnf(c_0_143,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_45]),c_0_96])])).

fof(c_0_144,plain,(
    ! [X58,X59] :
      ( ~ v2_pre_topc(X58)
      | ~ l1_pre_topc(X58)
      | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
      | v3_pre_topc(k1_tops_1(X58,X59),X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_145,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,k9_subset_1(esk2_0,esk2_0,X1)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_137])])).

cnf(c_0_146,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_106])).

cnf(c_0_148,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),X1),k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_140,c_0_133])).

cnf(c_0_149,negated_conjecture,
    ( k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_141]),c_0_142])])).

cnf(c_0_150,negated_conjecture,
    ( r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_45]),c_0_37])])).

cnf(c_0_151,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_152,plain,
    ( k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_88])).

cnf(c_0_153,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_98])).

cnf(c_0_154,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_144])).

cnf(c_0_155,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_139]),c_0_146])).

cnf(c_0_156,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_157,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | ~ r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_147])).

cnf(c_0_158,negated_conjecture,
    ( r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_37])]),c_0_150])).

cnf(c_0_159,negated_conjecture,
    ( k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0)
    | ~ r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_151,c_0_152])).

cnf(c_0_160,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_45]),c_0_96])])).

cnf(c_0_161,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_156]),c_0_96])])).

cnf(c_0_162,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_157,c_0_158])])).

cnf(c_0_163,plain,
    ( k4_xboole_0(k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) = k2_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_152]),c_0_153])).

cnf(c_0_164,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_105]),c_0_53])).

cnf(c_0_165,negated_conjecture,
    ( k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159,c_0_160])])).

cnf(c_0_166,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_161,c_0_162]),c_0_162]),c_0_162])).

cnf(c_0_167,negated_conjecture,
    ( k4_xboole_0(k2_pre_topc(esk1_0,k4_xboole_0(esk2_0,X1)),k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1))) = k2_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_164]),c_0_96])])).

cnf(c_0_168,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_106,c_0_162])).

cnf(c_0_169,negated_conjecture,
    ( k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0) != k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_165,c_0_166])])).

cnf(c_0_170,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_168]),c_0_162]),c_0_169]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 16.84/17.02  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 16.84/17.02  # and selection function SelectMaxLComplexAvoidPosPred.
% 16.84/17.02  #
% 16.84/17.02  # Preprocessing time       : 0.028 s
% 16.84/17.02  # Presaturation interreduction done
% 16.84/17.02  
% 16.84/17.02  # Proof found!
% 16.84/17.02  # SZS status Theorem
% 16.84/17.02  # SZS output start CNFRefutation
% 16.84/17.02  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.84/17.02  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 16.84/17.02  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 16.84/17.02  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 16.84/17.02  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 16.84/17.02  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 16.84/17.02  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 16.84/17.02  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.84/17.02  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 16.84/17.02  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 16.84/17.02  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 16.84/17.02  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 16.84/17.02  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 16.84/17.02  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 16.84/17.02  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 16.84/17.02  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 16.84/17.02  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 16.84/17.02  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 16.84/17.02  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 16.84/17.02  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 16.84/17.02  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 16.84/17.02  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 16.84/17.02  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 16.84/17.02  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 16.84/17.02  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 16.84/17.02  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 16.84/17.02  fof(c_0_26, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 16.84/17.02  fof(c_0_27, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 16.84/17.02  fof(c_0_28, plain, ![X14, X15, X16]:(~r1_tarski(X14,k2_xboole_0(X15,X16))|r1_tarski(k4_xboole_0(X14,X15),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 16.84/17.02  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 16.84/17.02  fof(c_0_30, plain, ![X28]:m1_subset_1(k2_subset_1(X28),k1_zfmisc_1(X28)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 16.84/17.02  fof(c_0_31, plain, ![X25]:k2_subset_1(X25)=X25, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 16.84/17.02  fof(c_0_32, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(X22))|k9_subset_1(X22,X23,X24)=k9_subset_1(X22,X24,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 16.84/17.02  fof(c_0_33, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 16.84/17.02  fof(c_0_34, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(X42))|k9_subset_1(X42,X43,X44)=k3_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 16.84/17.02  fof(c_0_35, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 16.84/17.02  cnf(c_0_36, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 16.84/17.02  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_29])).
% 16.84/17.02  fof(c_0_38, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 16.84/17.02  fof(c_0_39, plain, ![X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|k3_subset_1(X26,X27)=k4_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 16.84/17.02  fof(c_0_40, plain, ![X48]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X48)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 16.84/17.02  cnf(c_0_41, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 16.84/17.02  cnf(c_0_42, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 16.84/17.02  fof(c_0_43, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(X31))|m1_subset_1(k9_subset_1(X31,X32,X33),k1_zfmisc_1(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 16.84/17.02  cnf(c_0_44, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 16.84/17.02  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 16.84/17.02  cnf(c_0_46, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 16.84/17.02  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 16.84/17.02  fof(c_0_48, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 16.84/17.02  fof(c_0_49, plain, ![X11, X12]:r1_tarski(k4_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 16.84/17.02  fof(c_0_50, plain, ![X49, X50]:((~m1_subset_1(X49,k1_zfmisc_1(X50))|r1_tarski(X49,X50))&(~r1_tarski(X49,X50)|m1_subset_1(X49,k1_zfmisc_1(X50)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 16.84/17.02  fof(c_0_51, plain, ![X17, X18, X19]:(~r1_tarski(k4_xboole_0(X17,X18),X19)|r1_tarski(X17,k2_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 16.84/17.02  cnf(c_0_52, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 16.84/17.02  cnf(c_0_53, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 16.84/17.02  fof(c_0_54, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 16.84/17.02  fof(c_0_55, plain, ![X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|k3_subset_1(X37,k3_subset_1(X37,X38))=X38), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 16.84/17.02  cnf(c_0_56, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 16.84/17.02  cnf(c_0_57, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 16.84/17.02  cnf(c_0_58, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 16.84/17.02  cnf(c_0_59, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 16.84/17.02  cnf(c_0_60, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 16.84/17.02  cnf(c_0_61, plain, (k9_subset_1(X2,X3,X1)=k4_xboole_0(X3,k4_xboole_0(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 16.84/17.02  cnf(c_0_62, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 16.84/17.02  cnf(c_0_63, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 16.84/17.02  cnf(c_0_64, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 16.84/17.02  cnf(c_0_65, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 16.84/17.02  cnf(c_0_66, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 16.84/17.02  cnf(c_0_67, plain, (r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 16.84/17.02  cnf(c_0_68, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 16.84/17.02  cnf(c_0_69, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 16.84/17.02  cnf(c_0_70, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_53])).
% 16.84/17.02  cnf(c_0_71, plain, (k3_subset_1(X1,X1)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_56, c_0_58])).
% 16.84/17.02  fof(c_0_72, plain, ![X39, X40, X41]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|k7_subset_1(X39,X40,X41)=k4_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 16.84/17.02  cnf(c_0_73, negated_conjecture, (m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_45])])).
% 16.84/17.02  cnf(c_0_74, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)=k4_xboole_0(X1,k4_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_61, c_0_45])).
% 16.84/17.02  cnf(c_0_75, plain, (k9_subset_1(X1,X2,X1)=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_61, c_0_58])).
% 16.84/17.02  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 16.84/17.02  fof(c_0_77, plain, ![X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(X29))|m1_subset_1(k3_subset_1(X29,X30),k1_zfmisc_1(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 16.84/17.02  cnf(c_0_78, plain, (k9_subset_1(X1,X1,X2)=k9_subset_1(X1,X2,X1)), inference(spm,[status(thm)],[c_0_44, c_0_58])).
% 16.84/17.02  cnf(c_0_79, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_57])).
% 16.84/17.02  cnf(c_0_80, plain, (k2_xboole_0(X1,X2)=X3|~r1_tarski(k2_xboole_0(X1,X2),X3)|~r1_tarski(k4_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 16.84/17.02  cnf(c_0_81, plain, (r1_tarski(k2_xboole_0(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 16.84/17.02  cnf(c_0_82, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_57]), c_0_70]), c_0_71])).
% 16.84/17.02  fof(c_0_83, plain, ![X67, X68]:(~l1_pre_topc(X67)|(~m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))|k1_tops_1(X67,X68)=k7_subset_1(u1_struct_0(X67),X68,k2_tops_1(X67,X68)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 16.84/17.02  cnf(c_0_84, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 16.84/17.02  fof(c_0_85, plain, ![X54, X55]:(~l1_pre_topc(X54)|~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))|m1_subset_1(k2_pre_topc(X54,X55),k1_zfmisc_1(u1_struct_0(X54)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 16.84/17.02  cnf(c_0_86, negated_conjecture, (m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_73, c_0_60])).
% 16.84/17.02  cnf(c_0_87, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)=k9_subset_1(esk2_0,X1,esk2_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 16.84/17.02  cnf(c_0_88, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 16.84/17.02  cnf(c_0_89, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_76, c_0_63])).
% 16.84/17.02  cnf(c_0_90, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 16.84/17.02  cnf(c_0_91, plain, (m1_subset_1(k9_subset_1(X1,X1,X2),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_78]), c_0_58])])).
% 16.84/17.02  cnf(c_0_92, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_79])).
% 16.84/17.02  cnf(c_0_93, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X3),X1),X2)), inference(spm,[status(thm)],[c_0_36, c_0_63])).
% 16.84/17.02  cnf(c_0_94, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_79])])).
% 16.84/17.02  cnf(c_0_95, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 16.84/17.02  cnf(c_0_96, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 16.84/17.02  cnf(c_0_97, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_84, c_0_45])).
% 16.84/17.02  cnf(c_0_98, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 16.84/17.02  cnf(c_0_99, negated_conjecture, (m1_subset_1(k9_subset_1(esk2_0,X1,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[c_0_86, c_0_87])).
% 16.84/17.02  cnf(c_0_100, plain, (k9_subset_1(X1,X2,X3)=k4_xboole_0(X2,k4_xboole_0(X2,X3))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_61, c_0_88])).
% 16.84/17.02  cnf(c_0_101, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X3),X4),X1),X2)), inference(spm,[status(thm)],[c_0_36, c_0_89])).
% 16.84/17.02  cnf(c_0_102, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_64, c_0_90])).
% 16.84/17.02  cnf(c_0_103, plain, (k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_44, c_0_88])).
% 16.84/17.02  cnf(c_0_104, plain, (m1_subset_1(k9_subset_1(X1,X2,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_91, c_0_78])).
% 16.84/17.02  cnf(c_0_105, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 16.84/17.02  cnf(c_0_106, negated_conjecture, (k4_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_45]), c_0_96])]), c_0_97])).
% 16.84/17.02  cnf(c_0_107, plain, (k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3)=k4_xboole_0(k2_pre_topc(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_84, c_0_98])).
% 16.84/17.02  fof(c_0_108, plain, ![X56, X57]:(~l1_pre_topc(X56)|(~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))|r1_tarski(X57,k2_pre_topc(X56,X57)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 16.84/17.02  fof(c_0_109, plain, ![X60, X61]:(~l1_pre_topc(X60)|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))|k2_tops_1(X60,X61)=k7_subset_1(u1_struct_0(X60),k2_pre_topc(X60,X61),k1_tops_1(X60,X61)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 16.84/17.02  cnf(c_0_110, negated_conjecture, (m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_37])])).
% 16.84/17.02  cnf(c_0_111, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_101]), c_0_94])).
% 16.84/17.02  cnf(c_0_112, plain, (k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_56, c_0_88])).
% 16.84/17.02  cnf(c_0_113, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_69, c_0_88])).
% 16.84/17.02  cnf(c_0_114, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_102, c_0_88])).
% 16.84/17.02  cnf(c_0_115, negated_conjecture, (m1_subset_1(k9_subset_1(esk2_0,esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_103]), c_0_37])])).
% 16.84/17.02  cnf(c_0_116, plain, (r1_tarski(k9_subset_1(X1,X2,X3),X1)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_64, c_0_59])).
% 16.84/17.02  cnf(c_0_117, plain, (m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_100]), c_0_37])])).
% 16.84/17.02  cnf(c_0_118, negated_conjecture, (k4_xboole_0(k1_tops_1(esk1_0,esk2_0),esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 16.84/17.02  cnf(c_0_119, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 16.84/17.02  cnf(c_0_120, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),X1)=k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_45]), c_0_96])])).
% 16.84/17.02  cnf(c_0_121, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_108])).
% 16.84/17.02  cnf(c_0_122, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_109])).
% 16.84/17.02  fof(c_0_123, plain, ![X62, X63, X64]:(~l1_pre_topc(X62)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X62)))|(~v3_pre_topc(X63,X62)|~r1_tarski(X63,X64)|r1_tarski(X63,k1_tops_1(X62,X64)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 16.84/17.02  cnf(c_0_124, negated_conjecture, (m1_subset_1(k4_xboole_0(k4_xboole_0(esk2_0,X1),X2),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_53])).
% 16.84/17.02  cnf(c_0_125, plain, (k4_xboole_0(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114])).
% 16.84/17.02  cnf(c_0_126, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,esk2_0,X1),X2)=k4_xboole_0(k9_subset_1(esk2_0,esk2_0,X1),X2)), inference(spm,[status(thm)],[c_0_84, c_0_115])).
% 16.84/17.02  cnf(c_0_127, plain, (r1_tarski(k9_subset_1(X1,X2,X1),X1)), inference(spm,[status(thm)],[c_0_116, c_0_58])).
% 16.84/17.02  cnf(c_0_128, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_53])).
% 16.84/17.02  cnf(c_0_129, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_66, c_0_68])).
% 16.84/17.02  cnf(c_0_130, plain, (k3_subset_1(X1,k4_xboole_0(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_113, c_0_112])).
% 16.84/17.02  cnf(c_0_131, negated_conjecture, (k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)|v3_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_119, c_0_120])).
% 16.84/17.02  cnf(c_0_132, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_45]), c_0_96])])).
% 16.84/17.02  cnf(c_0_133, negated_conjecture, (k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_120]), c_0_96]), c_0_45])])).
% 16.84/17.02  cnf(c_0_134, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 16.84/17.02  cnf(c_0_135, negated_conjecture, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 16.84/17.02  cnf(c_0_136, negated_conjecture, (k4_xboole_0(k9_subset_1(esk2_0,esk2_0,X1),k2_tops_1(esk1_0,k9_subset_1(esk2_0,esk2_0,X1)))=k1_tops_1(esk1_0,k9_subset_1(esk2_0,esk2_0,X1))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_115]), c_0_96])]), c_0_126])).
% 16.84/17.02  cnf(c_0_137, plain, (r1_tarski(k9_subset_1(X1,X1,X2),X1)), inference(spm,[status(thm)],[c_0_127, c_0_78])).
% 16.84/17.02  cnf(c_0_138, negated_conjecture, (k9_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_118]), c_0_53]), c_0_78])).
% 16.84/17.02  cnf(c_0_139, negated_conjecture, (k9_subset_1(esk2_0,X1,k1_tops_1(esk1_0,esk2_0))=k4_xboole_0(X1,k4_xboole_0(X1,k1_tops_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_61, c_0_128])).
% 16.84/17.02  cnf(c_0_140, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(k4_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_36, c_0_129])).
% 16.84/17.02  cnf(c_0_141, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=esk2_0|v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_132])])).
% 16.84/17.02  cnf(c_0_142, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_63, c_0_133])).
% 16.84/17.02  cnf(c_0_143, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_45]), c_0_96])])).
% 16.84/17.02  fof(c_0_144, plain, ![X58, X59]:(~v2_pre_topc(X58)|~l1_pre_topc(X58)|~m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))|v3_pre_topc(k1_tops_1(X58,X59),X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 16.84/17.02  cnf(c_0_145, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,k9_subset_1(esk2_0,esk2_0,X1)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_137])])).
% 16.84/17.02  cnf(c_0_146, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0)))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_138, c_0_139])).
% 16.84/17.02  cnf(c_0_147, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_63, c_0_106])).
% 16.84/17.02  cnf(c_0_148, negated_conjecture, (r1_tarski(k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),X1),k1_tops_1(esk1_0,esk2_0))|~r1_tarski(k2_tops_1(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_140, c_0_133])).
% 16.84/17.02  cnf(c_0_149, negated_conjecture, (k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=esk2_0|v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_141]), c_0_142])])).
% 16.84/17.02  cnf(c_0_150, negated_conjecture, (r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_45]), c_0_37])])).
% 16.84/17.02  cnf(c_0_151, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 16.84/17.02  cnf(c_0_152, plain, (k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_84, c_0_88])).
% 16.84/17.02  cnf(c_0_153, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_64, c_0_98])).
% 16.84/17.02  cnf(c_0_154, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_144])).
% 16.84/17.02  cnf(c_0_155, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_139]), c_0_146])).
% 16.84/17.02  cnf(c_0_156, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 16.84/17.02  cnf(c_0_157, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|~r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_65, c_0_147])).
% 16.84/17.02  cnf(c_0_158, negated_conjecture, (r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_37])]), c_0_150])).
% 16.84/17.02  cnf(c_0_159, negated_conjecture, (k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)|~r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_151, c_0_152])).
% 16.84/17.02  cnf(c_0_160, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_45]), c_0_96])])).
% 16.84/17.02  cnf(c_0_161, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_155]), c_0_156]), c_0_96])])).
% 16.84/17.02  cnf(c_0_162, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_157, c_0_158])])).
% 16.84/17.02  cnf(c_0_163, plain, (k4_xboole_0(k2_pre_topc(X1,X2),k1_tops_1(X1,X2))=k2_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_152]), c_0_153])).
% 16.84/17.02  cnf(c_0_164, negated_conjecture, (m1_subset_1(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_105]), c_0_53])).
% 16.84/17.02  cnf(c_0_165, negated_conjecture, (k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159, c_0_160])])).
% 16.84/17.02  cnf(c_0_166, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_161, c_0_162]), c_0_162]), c_0_162])).
% 16.84/17.02  cnf(c_0_167, negated_conjecture, (k4_xboole_0(k2_pre_topc(esk1_0,k4_xboole_0(esk2_0,X1)),k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)))=k2_tops_1(esk1_0,k4_xboole_0(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_164]), c_0_96])])).
% 16.84/17.02  cnf(c_0_168, negated_conjecture, (k4_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_106, c_0_162])).
% 16.84/17.02  cnf(c_0_169, negated_conjecture, (k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)!=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_165, c_0_166])])).
% 16.84/17.02  cnf(c_0_170, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_168]), c_0_162]), c_0_169]), ['proof']).
% 16.84/17.02  # SZS output end CNFRefutation
% 16.84/17.02  # Proof object total steps             : 171
% 16.84/17.02  # Proof object clause steps            : 118
% 16.84/17.02  # Proof object formula steps           : 53
% 16.84/17.02  # Proof object conjectures             : 53
% 16.84/17.02  # Proof object clause conjectures      : 50
% 16.84/17.02  # Proof object formula conjectures     : 3
% 16.84/17.02  # Proof object initial clauses used    : 32
% 16.84/17.02  # Proof object initial formulas used   : 26
% 16.84/17.02  # Proof object generating inferences   : 75
% 16.84/17.02  # Proof object simplifying inferences  : 77
% 16.84/17.02  # Training examples: 0 positive, 0 negative
% 16.84/17.02  # Parsed axioms                        : 30
% 16.84/17.02  # Removed by relevancy pruning/SinE    : 0
% 16.84/17.02  # Initial clauses                      : 37
% 16.84/17.02  # Removed in clause preprocessing      : 2
% 16.84/17.02  # Initial clauses in saturation        : 35
% 16.84/17.02  # Processed clauses                    : 79943
% 16.84/17.02  # ...of these trivial                  : 2753
% 16.84/17.02  # ...subsumed                          : 67920
% 16.84/17.02  # ...remaining for further processing  : 9270
% 16.84/17.02  # Other redundant clauses eliminated   : 2
% 16.84/17.02  # Clauses deleted for lack of memory   : 0
% 16.84/17.02  # Backward-subsumed                    : 748
% 16.84/17.02  # Backward-rewritten                   : 1467
% 16.84/17.02  # Generated clauses                    : 2337106
% 16.84/17.02  # ...of the previous two non-trivial   : 1933307
% 16.84/17.02  # Contextual simplify-reflections      : 134
% 16.84/17.02  # Paramodulations                      : 2337104
% 16.84/17.02  # Factorizations                       : 0
% 16.84/17.02  # Equation resolutions                 : 2
% 16.84/17.02  # Propositional unsat checks           : 0
% 16.84/17.02  #    Propositional check models        : 0
% 16.84/17.02  #    Propositional check unsatisfiable : 0
% 16.84/17.02  #    Propositional clauses             : 0
% 16.84/17.02  #    Propositional clauses after purity: 0
% 16.84/17.02  #    Propositional unsat core size     : 0
% 16.84/17.02  #    Propositional preprocessing time  : 0.000
% 16.84/17.02  #    Propositional encoding time       : 0.000
% 16.84/17.02  #    Propositional solver time         : 0.000
% 16.84/17.02  #    Success case prop preproc time    : 0.000
% 16.84/17.02  #    Success case prop encoding time   : 0.000
% 16.84/17.02  #    Success case prop solver time     : 0.000
% 16.84/17.02  # Current number of processed clauses  : 7019
% 16.84/17.02  #    Positive orientable unit clauses  : 1998
% 16.84/17.02  #    Positive unorientable unit clauses: 82
% 16.84/17.02  #    Negative unit clauses             : 19
% 16.84/17.02  #    Non-unit-clauses                  : 4920
% 16.84/17.02  # Current number of unprocessed clauses: 1847089
% 16.84/17.02  # ...number of literals in the above   : 4511523
% 16.84/17.02  # Current number of archived formulas  : 0
% 16.84/17.02  # Current number of archived clauses   : 2251
% 16.84/17.02  # Clause-clause subsumption calls (NU) : 4753202
% 16.84/17.02  # Rec. Clause-clause subsumption calls : 4329325
% 16.84/17.02  # Non-unit clause-clause subsumptions  : 52301
% 16.84/17.02  # Unit Clause-clause subsumption calls : 43129
% 16.84/17.02  # Rewrite failures with RHS unbound    : 0
% 16.84/17.02  # BW rewrite match attempts            : 85649
% 16.84/17.02  # BW rewrite match successes           : 635
% 16.84/17.02  # Condensation attempts                : 0
% 16.84/17.02  # Condensation successes               : 0
% 16.84/17.02  # Termbank termtop insertions          : 41643667
% 16.84/17.08  
% 16.84/17.08  # -------------------------------------------------
% 16.84/17.08  # User time                : 16.009 s
% 16.84/17.08  # System time              : 0.721 s
% 16.84/17.08  # Total time               : 16.731 s
% 16.84/17.08  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
