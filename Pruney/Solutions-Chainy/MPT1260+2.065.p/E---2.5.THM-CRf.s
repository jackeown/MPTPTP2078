%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 (3477 expanded)
%              Number of clauses        :   79 (1705 expanded)
%              Number of leaves         :   20 ( 868 expanded)
%              Depth                    :   21
%              Number of atoms          :  297 (7287 expanded)
%              Number of equality atoms :   98 (3872 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

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

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(c_0_20,plain,(
    ! [X26,X27] : k4_xboole_0(X26,X27) = k5_xboole_0(X26,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X42,X43] : k1_setfam_1(k2_tarski(X42,X43)) = k3_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_22,plain,(
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

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_27,plain,(
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

cnf(c_0_28,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_30,plain,(
    ! [X29] : k4_xboole_0(k1_xboole_0,X29) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( X1 = k1_setfam_1(k2_tarski(X2,X3))
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk1_3(X2,X3,X1),k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X3)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_36,plain,
    ( X1 = k1_setfam_1(k2_tarski(X2,X3))
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk1_3(X2,X3,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_37,plain,(
    ! [X30,X31] : k2_xboole_0(X30,X31) = k5_xboole_0(X30,k4_xboole_0(X31,X30)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_38,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | k7_subset_1(X39,X40,X41) = k4_xboole_0(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_39,plain,(
    ! [X35,X36] : m1_subset_1(k6_subset_1(X35,X36),k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_40,plain,(
    ! [X37,X38] : k6_subset_1(X37,X38) = k4_xboole_0(X37,X38) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_41,plain,
    ( X1 = k1_setfam_1(k2_tarski(X2,k1_xboole_0))
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

fof(c_0_42,plain,(
    ! [X28] : k2_xboole_0(X28,k1_xboole_0) = X28 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( X1 = k1_setfam_1(k2_tarski(X2,k1_xboole_0))
    | ~ r2_hidden(esk1_3(X2,k1_xboole_0,X1),k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_41])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_26])).

cnf(c_0_50,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_51,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_26])).

cnf(c_0_52,plain,
    ( X1 = k1_setfam_1(k2_tarski(X2,k1_xboole_0))
    | ~ r2_hidden(esk1_3(X2,k1_xboole_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_35])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_54,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

cnf(c_0_55,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3))) = k7_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_41])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_53,c_0_35])).

fof(c_0_59,plain,(
    ! [X46,X47] :
      ( ~ l1_pre_topc(X46)
      | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
      | m1_subset_1(k2_tops_1(X46,X47),k1_zfmisc_1(u1_struct_0(X46))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

fof(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) )
    & ( v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).

cnf(c_0_61,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_55,c_0_26])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_58]),c_0_58])).

cnf(c_0_63,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_64,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | ~ m1_subset_1(X34,k1_zfmisc_1(X32))
      | m1_subset_1(k4_subset_1(X32,X33,X34),k1_zfmisc_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_65,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_68,plain,(
    ! [X55,X56] :
      ( ~ l1_pre_topc(X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
      | k2_pre_topc(X55,X56) = k4_subset_1(u1_struct_0(X55),X56,k2_tops_1(X55,X56)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_69,plain,(
    ! [X52,X53,X54] :
      ( ~ l1_pre_topc(X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X52)))
      | ~ v3_pre_topc(X53,X52)
      | ~ r1_tarski(X53,X54)
      | r1_tarski(X53,k1_tops_1(X52,X54)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

fof(c_0_70,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(X24,X25)
        | X24 != X25 )
      & ( r1_tarski(X25,X24)
        | X24 != X25 )
      & ( ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X25,X24)
        | X24 = X25 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_71,plain,(
    ! [X57,X58] :
      ( ~ l1_pre_topc(X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
      | k1_tops_1(X57,X58) = k7_subset_1(u1_struct_0(X57),X58,k2_tops_1(X57,X58)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_72,plain,
    ( X1 = k7_subset_1(X2,X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),X2)
    | r2_hidden(esk2_3(X2,X3,X1),X1) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_73,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_63,c_0_26])).

cnf(c_0_74,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_76,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_66])).

cnf(c_0_80,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,k7_subset_1(X2,X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_31,c_0_62])).

cnf(c_0_82,plain,
    ( k7_subset_1(X1,X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_72])).

cnf(c_0_83,plain,
    ( X1 = k7_subset_1(X2,X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),X3)
    | ~ r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk2_3(X2,X3,X1),X2) ),
    inference(rw,[status(thm)],[c_0_73,c_0_62])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k4_subset_1(u1_struct_0(esk3_0),X1,k2_tops_1(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k2_pre_topc(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_66]),c_0_67])])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_66]),c_0_67])])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_78])).

fof(c_0_88,plain,(
    ! [X44,X45] :
      ( ( ~ m1_subset_1(X44,k1_zfmisc_1(X45))
        | r1_tarski(X44,X45) )
      & ( ~ r1_tarski(X44,X45)
        | m1_subset_1(X44,k1_zfmisc_1(X45)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_79])).

cnf(c_0_90,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_66]),c_0_67])])).

cnf(c_0_91,plain,
    ( k7_subset_1(X1,X1,X2) = X1
    | ~ r2_hidden(esk2_3(X1,X2,X1),k7_subset_1(X3,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_92,plain,
    ( k7_subset_1(X1,X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_82]),c_0_82])).

cnf(c_0_93,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_62])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_66]),c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_66]),c_0_87])])).

cnf(c_0_96,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

fof(c_0_99,plain,(
    ! [X48,X49] :
      ( ~ v2_pre_topc(X48)
      | ~ l1_pre_topc(X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
      | v3_pre_topc(k1_tops_1(X48,X49),X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_100,plain,
    ( k7_subset_1(X1,X1,k7_subset_1(X2,X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( k7_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk4_0),X1) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_102,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_103,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0)
    | r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) = k7_subset_1(esk4_0,esk4_0,X1) ),
    inference(rw,[status(thm)],[c_0_79,c_0_62])).

cnf(c_0_106,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_107,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_108,negated_conjecture,
    ( k7_subset_1(X1,X1,k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_109,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0)
    | k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])])).

cnf(c_0_110,negated_conjecture,
    ( k7_subset_1(esk4_0,esk4_0,k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_90,c_0_105])).

fof(c_0_111,plain,(
    ! [X50,X51] :
      ( ~ l1_pre_topc(X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
      | k2_tops_1(X50,X51) = k7_subset_1(u1_struct_0(X50),k2_pre_topc(X50,X51),k1_tops_1(X50,X51)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_112,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_66]),c_0_107]),c_0_67])])).

cnf(c_0_113,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110])])).

cnf(c_0_114,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_116,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_117,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),k1_tops_1(esk3_0,esk4_0)) = k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_66]),c_0_67])])).

cnf(c_0_118,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) != k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116])])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_113]),c_0_118]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.20/0.50  # and selection function SelectCQArNTNpEqFirst.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.029 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.50  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.50  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.50  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.50  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.50  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.50  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.20/0.50  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.20/0.50  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.20/0.50  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.50  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 0.20/0.50  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.20/0.50  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.20/0.50  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 0.20/0.50  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 0.20/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.50  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 0.20/0.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.50  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.20/0.50  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 0.20/0.50  fof(c_0_20, plain, ![X26, X27]:k4_xboole_0(X26,X27)=k5_xboole_0(X26,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.50  fof(c_0_21, plain, ![X42, X43]:k1_setfam_1(k2_tarski(X42,X43))=k3_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.50  fof(c_0_22, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k4_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k4_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))&(~r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.50  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.50  cnf(c_0_24, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.50  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.50  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.50  fof(c_0_27, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.50  cnf(c_0_28, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.50  cnf(c_0_29, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.50  fof(c_0_30, plain, ![X29]:k4_xboole_0(k1_xboole_0,X29)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.50  cnf(c_0_31, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.50  cnf(c_0_32, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_29, c_0_24])).
% 0.20/0.50  cnf(c_0_33, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.50  cnf(c_0_34, plain, (X1=k1_setfam_1(k2_tarski(X2,X3))|r2_hidden(esk1_3(X2,X3,X1),X1)|~r2_hidden(esk1_3(X2,X3,X1),k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X3))))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.50  cnf(c_0_35, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_33, c_0_26])).
% 0.20/0.50  cnf(c_0_36, plain, (X1=k1_setfam_1(k2_tarski(X2,X3))|r2_hidden(esk1_3(X2,X3,X1),X1)|~r2_hidden(esk1_3(X2,X3,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.50  fof(c_0_37, plain, ![X30, X31]:k2_xboole_0(X30,X31)=k5_xboole_0(X30,k4_xboole_0(X31,X30)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.50  fof(c_0_38, plain, ![X39, X40, X41]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|k7_subset_1(X39,X40,X41)=k4_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.20/0.50  fof(c_0_39, plain, ![X35, X36]:m1_subset_1(k6_subset_1(X35,X36),k1_zfmisc_1(X35)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.20/0.50  fof(c_0_40, plain, ![X37, X38]:k6_subset_1(X37,X38)=k4_xboole_0(X37,X38), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.20/0.50  cnf(c_0_41, plain, (X1=k1_setfam_1(k2_tarski(X2,k1_xboole_0))|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_36, c_0_32])).
% 0.20/0.50  fof(c_0_42, plain, ![X28]:k2_xboole_0(X28,k1_xboole_0)=X28, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.50  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.50  cnf(c_0_44, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.50  cnf(c_0_45, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.50  cnf(c_0_46, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.50  cnf(c_0_47, plain, (X1=k1_setfam_1(k2_tarski(X2,k1_xboole_0))|~r2_hidden(esk1_3(X2,k1_xboole_0,X1),k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1))))), inference(spm,[status(thm)],[c_0_31, c_0_41])).
% 0.20/0.50  cnf(c_0_48, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.50  cnf(c_0_49, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[c_0_43, c_0_26])).
% 0.20/0.50  cnf(c_0_50, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_44, c_0_26])).
% 0.20/0.50  cnf(c_0_51, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_26])).
% 0.20/0.50  cnf(c_0_52, plain, (X1=k1_setfam_1(k2_tarski(X2,k1_xboole_0))|~r2_hidden(esk1_3(X2,k1_xboole_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_35])).
% 0.20/0.50  cnf(c_0_53, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))))=X1), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.50  fof(c_0_54, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 0.20/0.50  cnf(c_0_55, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.50  cnf(c_0_56, plain, (k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)))=k7_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.50  cnf(c_0_57, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_41])).
% 0.20/0.50  cnf(c_0_58, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_53, c_0_35])).
% 0.20/0.50  fof(c_0_59, plain, ![X46, X47]:(~l1_pre_topc(X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))|m1_subset_1(k2_tops_1(X46,X47),k1_zfmisc_1(u1_struct_0(X46)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.20/0.50  fof(c_0_60, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))&(v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).
% 0.20/0.50  cnf(c_0_61, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_55, c_0_26])).
% 0.20/0.50  cnf(c_0_62, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k7_subset_1(X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_58]), c_0_58])).
% 0.20/0.50  cnf(c_0_63, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.50  fof(c_0_64, plain, ![X32, X33, X34]:(~m1_subset_1(X33,k1_zfmisc_1(X32))|~m1_subset_1(X34,k1_zfmisc_1(X32))|m1_subset_1(k4_subset_1(X32,X33,X34),k1_zfmisc_1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.20/0.50  cnf(c_0_65, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.50  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.50  cnf(c_0_67, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.50  fof(c_0_68, plain, ![X55, X56]:(~l1_pre_topc(X55)|(~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|k2_pre_topc(X55,X56)=k4_subset_1(u1_struct_0(X55),X56,k2_tops_1(X55,X56)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.20/0.50  fof(c_0_69, plain, ![X52, X53, X54]:(~l1_pre_topc(X52)|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))|(~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X52)))|(~v3_pre_topc(X53,X52)|~r1_tarski(X53,X54)|r1_tarski(X53,k1_tops_1(X52,X54)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 0.20/0.50  fof(c_0_70, plain, ![X24, X25]:(((r1_tarski(X24,X25)|X24!=X25)&(r1_tarski(X25,X24)|X24!=X25))&(~r1_tarski(X24,X25)|~r1_tarski(X25,X24)|X24=X25)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.50  fof(c_0_71, plain, ![X57, X58]:(~l1_pre_topc(X57)|(~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|k1_tops_1(X57,X58)=k7_subset_1(u1_struct_0(X57),X58,k2_tops_1(X57,X58)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.20/0.50  cnf(c_0_72, plain, (X1=k7_subset_1(X2,X2,X3)|r2_hidden(esk2_3(X2,X3,X1),X2)|r2_hidden(esk2_3(X2,X3,X1),X1)), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.50  cnf(c_0_73, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_63, c_0_26])).
% 0.20/0.50  cnf(c_0_74, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.50  cnf(c_0_75, negated_conjecture, (m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.20/0.50  cnf(c_0_76, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.50  cnf(c_0_77, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.50  cnf(c_0_78, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.50  cnf(c_0_79, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_66])).
% 0.20/0.50  cnf(c_0_80, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.50  cnf(c_0_81, plain, (~r2_hidden(X1,k7_subset_1(X2,X2,X3))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_31, c_0_62])).
% 0.20/0.50  cnf(c_0_82, plain, (k7_subset_1(X1,X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_72])).
% 0.20/0.50  cnf(c_0_83, plain, (X1=k7_subset_1(X2,X2,X3)|r2_hidden(esk2_3(X2,X3,X1),X3)|~r2_hidden(esk2_3(X2,X3,X1),X1)|~r2_hidden(esk2_3(X2,X3,X1),X2)), inference(rw,[status(thm)],[c_0_73, c_0_62])).
% 0.20/0.50  cnf(c_0_84, negated_conjecture, (m1_subset_1(k4_subset_1(u1_struct_0(esk3_0),X1,k2_tops_1(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.50  cnf(c_0_85, negated_conjecture, (k4_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k2_pre_topc(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_66]), c_0_67])])).
% 0.20/0.50  cnf(c_0_86, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_66]), c_0_67])])).
% 0.20/0.50  cnf(c_0_87, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_78])).
% 0.20/0.50  fof(c_0_88, plain, ![X44, X45]:((~m1_subset_1(X44,k1_zfmisc_1(X45))|r1_tarski(X44,X45))&(~r1_tarski(X44,X45)|m1_subset_1(X44,k1_zfmisc_1(X45)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.50  cnf(c_0_89, negated_conjecture, (m1_subset_1(k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_79])).
% 0.20/0.50  cnf(c_0_90, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_66]), c_0_67])])).
% 0.20/0.50  cnf(c_0_91, plain, (k7_subset_1(X1,X1,X2)=X1|~r2_hidden(esk2_3(X1,X2,X1),k7_subset_1(X3,X3,X1))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.50  cnf(c_0_92, plain, (k7_subset_1(X1,X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_82]), c_0_82])).
% 0.20/0.50  cnf(c_0_93, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X2,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_50, c_0_62])).
% 0.20/0.50  cnf(c_0_94, negated_conjecture, (m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_66]), c_0_85])).
% 0.20/0.50  cnf(c_0_95, negated_conjecture, (r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))|~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_66]), c_0_87])])).
% 0.20/0.50  cnf(c_0_96, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.50  cnf(c_0_97, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.50  cnf(c_0_98, negated_conjecture, (m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.50  fof(c_0_99, plain, ![X48, X49]:(~v2_pre_topc(X48)|~l1_pre_topc(X48)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|v3_pre_topc(k1_tops_1(X48,X49),X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.20/0.50  cnf(c_0_100, plain, (k7_subset_1(X1,X1,k7_subset_1(X2,X2,X1))=X1), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.50  cnf(c_0_101, negated_conjecture, (k7_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk4_0),X1)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.20/0.50  cnf(c_0_102, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.50  cnf(c_0_103, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)|r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.20/0.50  cnf(c_0_104, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.20/0.50  cnf(c_0_105, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)=k7_subset_1(esk4_0,esk4_0,X1)), inference(rw,[status(thm)],[c_0_79, c_0_62])).
% 0.20/0.50  cnf(c_0_106, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.20/0.50  cnf(c_0_107, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.50  cnf(c_0_108, negated_conjecture, (k7_subset_1(X1,X1,k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1))=X1), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.20/0.50  cnf(c_0_109, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)|k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104])])).
% 0.20/0.50  cnf(c_0_110, negated_conjecture, (k7_subset_1(esk4_0,esk4_0,k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_90, c_0_105])).
% 0.20/0.50  fof(c_0_111, plain, ![X50, X51]:(~l1_pre_topc(X50)|(~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))|k2_tops_1(X50,X51)=k7_subset_1(u1_struct_0(X50),k2_pre_topc(X50,X51),k1_tops_1(X50,X51)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.20/0.50  cnf(c_0_112, negated_conjecture, (v3_pre_topc(k1_tops_1(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_66]), c_0_107]), c_0_67])])).
% 0.20/0.50  cnf(c_0_113, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110])])).
% 0.20/0.50  cnf(c_0_114, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_111])).
% 0.20/0.50  cnf(c_0_115, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.50  cnf(c_0_116, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_112, c_0_113])).
% 0.20/0.50  cnf(c_0_117, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),k1_tops_1(esk3_0,esk4_0))=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_66]), c_0_67])])).
% 0.20/0.50  cnf(c_0_118, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)!=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116])])).
% 0.20/0.50  cnf(c_0_119, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_113]), c_0_118]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 120
% 0.20/0.50  # Proof object clause steps            : 79
% 0.20/0.50  # Proof object formula steps           : 41
% 0.20/0.50  # Proof object conjectures             : 31
% 0.20/0.50  # Proof object clause conjectures      : 28
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 27
% 0.20/0.50  # Proof object initial formulas used   : 20
% 0.20/0.50  # Proof object generating inferences   : 30
% 0.20/0.50  # Proof object simplifying inferences  : 49
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 21
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 38
% 0.20/0.50  # Removed in clause preprocessing      : 4
% 0.20/0.50  # Initial clauses in saturation        : 34
% 0.20/0.50  # Processed clauses                    : 739
% 0.20/0.50  # ...of these trivial                  : 10
% 0.20/0.50  # ...subsumed                          : 116
% 0.20/0.50  # ...remaining for further processing  : 612
% 0.20/0.50  # Other redundant clauses eliminated   : 8
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 10
% 0.20/0.50  # Backward-rewritten                   : 80
% 0.20/0.50  # Generated clauses                    : 5679
% 0.20/0.50  # ...of the previous two non-trivial   : 5250
% 0.20/0.50  # Contextual simplify-reflections      : 3
% 0.20/0.50  # Paramodulations                      : 5663
% 0.20/0.50  # Factorizations                       : 8
% 0.20/0.50  # Equation resolutions                 : 8
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 481
% 0.20/0.50  #    Positive orientable unit clauses  : 327
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 1
% 0.20/0.50  #    Non-unit-clauses                  : 153
% 0.20/0.50  # Current number of unprocessed clauses: 4552
% 0.20/0.50  # ...number of literals in the above   : 7434
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 127
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 3799
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 2325
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 128
% 0.20/0.50  # Unit Clause-clause subsumption calls : 1251
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 3838
% 0.20/0.50  # BW rewrite match successes           : 29
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 167335
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.152 s
% 0.20/0.51  # System time              : 0.011 s
% 0.20/0.51  # Total time               : 0.163 s
% 0.20/0.51  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
