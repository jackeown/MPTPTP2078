%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:33 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :  120 (56220 expanded)
%              Number of clauses        :   87 (25194 expanded)
%              Number of leaves         :   16 (14540 expanded)
%              Depth                    :   24
%              Number of atoms          :  278 (120261 expanded)
%              Number of equality atoms :   79 (44560 expanded)
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

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t29_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d6_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_16,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X35,X36] : k1_setfam_1(k2_tarski(X35,X36)) = k3_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
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

fof(c_0_19,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | k3_subset_1(X21,X22) = k4_xboole_0(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_24,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tops_1])).

fof(c_0_28,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X29))
      | k9_subset_1(X29,X30,X31) = k3_xboole_0(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_26])).

fof(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v4_pre_topc(esk3_0,esk2_0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0) )
    & ( v4_pre_topc(esk3_0,esk2_0)
      | v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_33,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | ~ m1_subset_1(X34,k1_zfmisc_1(X32))
      | k7_subset_1(X32,X33,X34) = k9_subset_1(X32,X33,k3_subset_1(X32,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

cnf(c_0_34,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | m1_subset_1(k3_subset_1(X24,X25),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_21]),c_0_25]),c_0_25])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | r2_hidden(esk1_3(X1,X2,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X23] : m1_subset_1(k2_subset_1(X23),k1_zfmisc_1(X23)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_40,plain,(
    ! [X20] : k2_subset_1(X20) = X20 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_41,plain,(
    ! [X37] :
      ( ~ l1_struct_0(X37)
      | k2_struct_0(X37) = u1_struct_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_42,plain,(
    ! [X40] :
      ( ~ l1_pre_topc(X40)
      | l1_struct_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_43,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_45,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X2)))) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk2_0),esk3_0) = k3_subset_1(u1_struct_0(esk2_0),esk3_0)
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_50,plain,(
    ! [X38,X39] :
      ( ( ~ v4_pre_topc(X39,X38)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X38),k2_struct_0(X38),X39),X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) )
      & ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X38),k2_struct_0(X38),X39),X38)
        | v4_pre_topc(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).

cnf(c_0_51,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2))
    | ~ m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,X3))) = k7_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk2_0),k1_setfam_1(k2_tarski(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)))) = esk3_0
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k7_subset_1(X2,X1,X3))) = k7_subset_1(X2,X1,X3)
    | ~ m1_subset_1(k5_xboole_0(X1,k7_subset_1(X2,X1,X3)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk2_0),k7_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),esk3_0)) = esk3_0
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_54]),c_0_38]),c_0_56])])).

cnf(c_0_61,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X2),u1_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),esk3_0) = k3_subset_1(u1_struct_0(esk2_0),esk3_0)
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_38]),c_0_56])])).

cnf(c_0_64,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_65,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk2_0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_66,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk2_0)
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_38])]),c_0_65])).

fof(c_0_68,plain,(
    ! [X18,X19] : k2_tarski(X18,X19) = k2_tarski(X19,X18) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_69,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_70,negated_conjecture,
    ( ~ v4_pre_topc(esk3_0,esk2_0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_71,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0)
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_63]),c_0_64]),c_0_38])]),c_0_67])).

cnf(c_0_72,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_53])).

cnf(c_0_73,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_69,c_0_21])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_67])).

fof(c_0_76,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | ~ r2_hidden(X28,X27)
      | r2_hidden(X28,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_77,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k5_xboole_0(X2,k9_subset_1(X1,X2,X3)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_44])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k9_subset_1(X2,X1,X3)) = k3_subset_1(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_44])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,u1_struct_0(esk2_0))) = esk3_0
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_73]),c_0_75])])).

cnf(c_0_81,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_45])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_84,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_30]),c_0_45])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))))) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_73])).

cnf(c_0_86,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk2_0),esk3_0) = k3_subset_1(u1_struct_0(esk2_0),esk3_0)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_38])])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_38])).

cnf(c_0_88,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_44])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_83,c_0_21])).

cnf(c_0_90,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_73])).

cnf(c_0_91,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))))),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(X2,X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk2_0),esk3_0) = k3_subset_1(u1_struct_0(esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_75])])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_30])).

cnf(c_0_94,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_56])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,X2)
    | X3 != k3_subset_1(X2,k3_subset_1(X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_89,c_0_84])).

cnf(c_0_96,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)) = esk3_0
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_80]),c_0_38])])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(k1_setfam_1(k2_tarski(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_80]),c_0_38])]),c_0_92])).

cnf(c_0_98,plain,
    ( k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2))) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_93]),c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk2_0))
    | X2 != esk3_0
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_38])])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),k1_setfam_1(k2_tarski(esk3_0,u1_struct_0(esk2_0)))),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_73]),c_0_38])])).

cnf(c_0_101,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_31]),c_0_31])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk2_0))
    | X2 != esk3_0
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_87]),c_0_75])])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_90]),c_0_38])])).

cnf(c_0_104,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r2_hidden(esk1_3(X2,X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_73])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_75])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_96])).

cnf(c_0_107,plain,
    ( k7_subset_1(X1,X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))) = k1_setfam_1(k2_tarski(X2,k1_setfam_1(k2_tarski(X1,X3))))
    | ~ m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3))),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_108,plain,
    ( k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))))) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(X2,X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_85])).

cnf(c_0_109,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,u1_struct_0(esk2_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_110,plain,
    ( k5_xboole_0(X1,k3_subset_1(X1,k3_subset_1(X1,X2))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_84])).

cnf(c_0_111,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_105])])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_105])])).

cnf(c_0_113,plain,
    ( v4_pre_topc(k5_xboole_0(u1_struct_0(X1),k1_setfam_1(k2_tarski(u1_struct_0(X1),X2))),X1)
    | ~ v3_pre_topc(k1_setfam_1(k2_tarski(u1_struct_0(X1),k1_setfam_1(k2_tarski(u1_struct_0(X1),X2)))),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k5_xboole_0(u1_struct_0(X1),k1_setfam_1(k2_tarski(u1_struct_0(X1),X2))),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_107]),c_0_56])])).

cnf(c_0_114,negated_conjecture,
    ( k1_setfam_1(k2_tarski(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))) = k3_subset_1(u1_struct_0(esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_92]),c_0_38])])).

cnf(c_0_115,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112])])).

cnf(c_0_116,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115]),c_0_114]),c_0_64]),c_0_115]),c_0_38])]),c_0_65])).

cnf(c_0_117,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),esk3_0) = k3_subset_1(u1_struct_0(esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_114]),c_0_38]),c_0_56])])).

cnf(c_0_118,negated_conjecture,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_116])])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_117]),c_0_116]),c_0_64]),c_0_38])]),c_0_118]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:02:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 4.50/4.71  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 4.50/4.71  # and selection function PSelectComplexExceptUniqMaxHorn.
% 4.50/4.71  #
% 4.50/4.71  # Preprocessing time       : 0.028 s
% 4.50/4.71  
% 4.50/4.71  # Proof found!
% 4.50/4.71  # SZS status Theorem
% 4.50/4.71  # SZS output start CNFRefutation
% 4.50/4.71  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.50/4.71  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.50/4.71  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.50/4.71  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.50/4.71  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.50/4.71  fof(t29_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 4.50/4.71  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.50/4.71  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 4.50/4.71  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.50/4.71  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.50/4.71  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.50/4.71  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.50/4.71  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.50/4.71  fof(d6_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 4.50/4.71  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.50/4.71  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.50/4.71  fof(c_0_16, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 4.50/4.71  fof(c_0_17, plain, ![X35, X36]:k1_setfam_1(k2_tarski(X35,X36))=k3_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 4.50/4.71  fof(c_0_18, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 4.50/4.71  fof(c_0_19, plain, ![X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|k3_subset_1(X21,X22)=k4_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 4.50/4.71  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.50/4.71  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.50/4.71  cnf(c_0_22, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.50/4.71  fof(c_0_23, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 4.50/4.71  cnf(c_0_24, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.50/4.71  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 4.50/4.71  cnf(c_0_26, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 4.50/4.71  fof(c_0_27, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t29_tops_1])).
% 4.50/4.71  fof(c_0_28, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(X29))|k9_subset_1(X29,X30,X31)=k3_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 4.50/4.71  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.50/4.71  cnf(c_0_30, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 4.50/4.71  cnf(c_0_31, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_26])).
% 4.50/4.71  fof(c_0_32, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v4_pre_topc(esk3_0,esk2_0)|~v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0))&(v4_pre_topc(esk3_0,esk2_0)|v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 4.50/4.71  fof(c_0_33, plain, ![X32, X33, X34]:(~m1_subset_1(X33,k1_zfmisc_1(X32))|(~m1_subset_1(X34,k1_zfmisc_1(X32))|k7_subset_1(X32,X33,X34)=k9_subset_1(X32,X33,k3_subset_1(X32,X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 4.50/4.71  cnf(c_0_34, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.50/4.71  fof(c_0_35, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|m1_subset_1(k3_subset_1(X24,X25),k1_zfmisc_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 4.50/4.71  cnf(c_0_36, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_21]), c_0_25]), c_0_25])).
% 4.50/4.71  cnf(c_0_37, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|r2_hidden(esk1_3(X1,X2,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 4.50/4.71  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.50/4.71  fof(c_0_39, plain, ![X23]:m1_subset_1(k2_subset_1(X23),k1_zfmisc_1(X23)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 4.50/4.71  fof(c_0_40, plain, ![X20]:k2_subset_1(X20)=X20, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 4.50/4.71  fof(c_0_41, plain, ![X37]:(~l1_struct_0(X37)|k2_struct_0(X37)=u1_struct_0(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 4.50/4.71  fof(c_0_42, plain, ![X40]:(~l1_pre_topc(X40)|l1_struct_0(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 4.50/4.71  cnf(c_0_43, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.50/4.71  cnf(c_0_44, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_34, c_0_21])).
% 4.50/4.71  cnf(c_0_45, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 4.50/4.71  cnf(c_0_46, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X2))))=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_36, c_0_31])).
% 4.50/4.71  cnf(c_0_47, negated_conjecture, (k5_xboole_0(u1_struct_0(esk2_0),esk3_0)=k3_subset_1(u1_struct_0(esk2_0),esk3_0)|r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 4.50/4.71  cnf(c_0_48, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 4.50/4.71  cnf(c_0_49, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 4.50/4.71  fof(c_0_50, plain, ![X38, X39]:((~v4_pre_topc(X39,X38)|v3_pre_topc(k7_subset_1(u1_struct_0(X38),k2_struct_0(X38),X39),X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|~l1_pre_topc(X38))&(~v3_pre_topc(k7_subset_1(u1_struct_0(X38),k2_struct_0(X38),X39),X38)|v4_pre_topc(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|~l1_pre_topc(X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).
% 4.50/4.71  cnf(c_0_51, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.50/4.71  cnf(c_0_52, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 4.50/4.71  cnf(c_0_53, plain, (k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))|~m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_36])).
% 4.50/4.71  cnf(c_0_54, plain, (k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,X3)))=k7_subset_1(X2,X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 4.50/4.71  cnf(c_0_55, negated_conjecture, (k5_xboole_0(u1_struct_0(esk2_0),k1_setfam_1(k2_tarski(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))))=esk3_0|r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 4.50/4.71  cnf(c_0_56, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 4.50/4.71  cnf(c_0_57, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.50/4.71  cnf(c_0_58, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 4.50/4.71  cnf(c_0_59, plain, (k3_subset_1(X1,k5_xboole_0(X1,k7_subset_1(X2,X1,X3)))=k7_subset_1(X2,X1,X3)|~m1_subset_1(k5_xboole_0(X1,k7_subset_1(X2,X1,X3)),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 4.50/4.71  cnf(c_0_60, negated_conjecture, (k5_xboole_0(u1_struct_0(esk2_0),k7_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),esk3_0))=esk3_0|r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_54]), c_0_38]), c_0_56])])).
% 4.50/4.71  cnf(c_0_61, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.50/4.71  cnf(c_0_62, plain, (v4_pre_topc(X1,X2)|~v3_pre_topc(k7_subset_1(u1_struct_0(X2),u1_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 4.50/4.71  cnf(c_0_63, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),esk3_0)=k3_subset_1(u1_struct_0(esk2_0),esk3_0)|r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_38]), c_0_56])])).
% 4.50/4.71  cnf(c_0_64, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.50/4.71  cnf(c_0_65, negated_conjecture, (v4_pre_topc(esk3_0,esk2_0)|v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.50/4.71  cnf(c_0_66, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)|~v4_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_61, c_0_58])).
% 4.50/4.71  cnf(c_0_67, negated_conjecture, (v4_pre_topc(esk3_0,esk2_0)|r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_38])]), c_0_65])).
% 4.50/4.71  fof(c_0_68, plain, ![X18, X19]:k2_tarski(X18,X19)=k2_tarski(X19,X18), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 4.50/4.71  cnf(c_0_69, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.50/4.71  cnf(c_0_70, negated_conjecture, (~v4_pre_topc(esk3_0,esk2_0)|~v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.50/4.71  cnf(c_0_71, negated_conjecture, (v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0)|r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_63]), c_0_64]), c_0_38])]), c_0_67])).
% 4.50/4.71  cnf(c_0_72, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))|~m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_53])).
% 4.50/4.71  cnf(c_0_73, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 4.50/4.71  cnf(c_0_74, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_69, c_0_21])).
% 4.50/4.71  cnf(c_0_75, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_67])).
% 4.50/4.71  fof(c_0_76, plain, ![X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|(~r2_hidden(X28,X27)|r2_hidden(X28,X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 4.50/4.71  cnf(c_0_77, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X2))|~m1_subset_1(k5_xboole_0(X2,k9_subset_1(X1,X2,X3)),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_72, c_0_44])).
% 4.50/4.71  cnf(c_0_78, plain, (k5_xboole_0(X1,k9_subset_1(X2,X1,X3))=k3_subset_1(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_30, c_0_44])).
% 4.50/4.71  cnf(c_0_79, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_73])).
% 4.50/4.71  cnf(c_0_80, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,u1_struct_0(esk2_0)))=esk3_0|~r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_73]), c_0_75])])).
% 4.50/4.71  cnf(c_0_81, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 4.50/4.71  cnf(c_0_82, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_45])).
% 4.50/4.71  cnf(c_0_83, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.50/4.71  cnf(c_0_84, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_30]), c_0_45])).
% 4.50/4.71  cnf(c_0_85, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))))))=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_36, c_0_73])).
% 4.50/4.71  cnf(c_0_86, negated_conjecture, (k5_xboole_0(u1_struct_0(esk2_0),esk3_0)=k3_subset_1(u1_struct_0(esk2_0),esk3_0)|~r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_38])])).
% 4.50/4.71  cnf(c_0_87, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_81, c_0_38])).
% 4.50/4.71  cnf(c_0_88, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_82, c_0_44])).
% 4.50/4.71  cnf(c_0_89, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_83, c_0_21])).
% 4.50/4.71  cnf(c_0_90, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_84, c_0_73])).
% 4.50/4.71  cnf(c_0_91, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))))),k1_zfmisc_1(X1))|~m1_subset_1(k1_setfam_1(k2_tarski(X2,X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_72, c_0_85])).
% 4.50/4.71  cnf(c_0_92, negated_conjecture, (k5_xboole_0(u1_struct_0(esk2_0),esk3_0)=k3_subset_1(u1_struct_0(esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_75])])).
% 4.50/4.71  cnf(c_0_93, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_30])).
% 4.50/4.71  cnf(c_0_94, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_88, c_0_56])).
% 4.50/4.71  cnf(c_0_95, plain, (r2_hidden(X1,X2)|X3!=k3_subset_1(X2,k3_subset_1(X2,X4))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_89, c_0_84])).
% 4.50/4.71  cnf(c_0_96, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))=esk3_0|~r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_80]), c_0_38])])).
% 4.50/4.71  cnf(c_0_97, negated_conjecture, (m1_subset_1(k1_setfam_1(k2_tarski(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_80]), c_0_38])]), c_0_92])).
% 4.50/4.71  cnf(c_0_98, plain, (k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2)))=k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_93]), c_0_94])).
% 4.50/4.71  cnf(c_0_99, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk2_0))|X2!=esk3_0|~r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0))|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_38])])).
% 4.50/4.71  cnf(c_0_100, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),k1_setfam_1(k2_tarski(esk3_0,u1_struct_0(esk2_0)))),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_73]), c_0_38])])).
% 4.50/4.71  cnf(c_0_101, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_31]), c_0_31])).
% 4.50/4.71  cnf(c_0_102, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk2_0))|X2!=esk3_0|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_87]), c_0_75])])).
% 4.50/4.71  cnf(c_0_103, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_90]), c_0_38])])).
% 4.50/4.71  cnf(c_0_104, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r2_hidden(esk1_3(X2,X1,X1),X2)), inference(spm,[status(thm)],[c_0_101, c_0_73])).
% 4.50/4.71  cnf(c_0_105, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_102, c_0_75])).
% 4.50/4.71  cnf(c_0_106, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_103, c_0_96])).
% 4.50/4.71  cnf(c_0_107, plain, (k7_subset_1(X1,X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3))))=k1_setfam_1(k2_tarski(X2,k1_setfam_1(k2_tarski(X1,X3))))|~m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3))),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 4.50/4.71  cnf(c_0_108, plain, (k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))))=k3_subset_1(X1,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(k1_setfam_1(k2_tarski(X2,X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_85])).
% 4.50/4.71  cnf(c_0_109, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,u1_struct_0(esk2_0)))=esk3_0), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 4.50/4.71  cnf(c_0_110, plain, (k5_xboole_0(X1,k3_subset_1(X1,k3_subset_1(X1,X2)))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_84])).
% 4.50/4.71  cnf(c_0_111, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_105])])).
% 4.50/4.71  cnf(c_0_112, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_105])])).
% 4.50/4.71  cnf(c_0_113, plain, (v4_pre_topc(k5_xboole_0(u1_struct_0(X1),k1_setfam_1(k2_tarski(u1_struct_0(X1),X2))),X1)|~v3_pre_topc(k1_setfam_1(k2_tarski(u1_struct_0(X1),k1_setfam_1(k2_tarski(u1_struct_0(X1),X2)))),X1)|~l1_pre_topc(X1)|~m1_subset_1(k5_xboole_0(u1_struct_0(X1),k1_setfam_1(k2_tarski(u1_struct_0(X1),X2))),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_107]), c_0_56])])).
% 4.50/4.71  cnf(c_0_114, negated_conjecture, (k1_setfam_1(k2_tarski(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)))=k3_subset_1(u1_struct_0(esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_92]), c_0_38])])).
% 4.50/4.71  cnf(c_0_115, negated_conjecture, (k5_xboole_0(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112])])).
% 4.50/4.71  cnf(c_0_116, negated_conjecture, (v4_pre_topc(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115]), c_0_114]), c_0_64]), c_0_115]), c_0_38])]), c_0_65])).
% 4.50/4.71  cnf(c_0_117, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),esk3_0)=k3_subset_1(u1_struct_0(esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_114]), c_0_38]), c_0_56])])).
% 4.50/4.71  cnf(c_0_118, negated_conjecture, (~v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_116])])).
% 4.50/4.71  cnf(c_0_119, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_117]), c_0_116]), c_0_64]), c_0_38])]), c_0_118]), ['proof']).
% 4.50/4.71  # SZS output end CNFRefutation
% 4.50/4.71  # Proof object total steps             : 120
% 4.50/4.71  # Proof object clause steps            : 87
% 4.50/4.71  # Proof object formula steps           : 33
% 4.50/4.71  # Proof object conjectures             : 35
% 4.50/4.71  # Proof object clause conjectures      : 32
% 4.50/4.71  # Proof object formula conjectures     : 3
% 4.50/4.71  # Proof object initial clauses used    : 22
% 4.50/4.71  # Proof object initial formulas used   : 16
% 4.50/4.71  # Proof object generating inferences   : 54
% 4.50/4.71  # Proof object simplifying inferences  : 79
% 4.50/4.71  # Training examples: 0 positive, 0 negative
% 4.50/4.71  # Parsed axioms                        : 16
% 4.50/4.71  # Removed by relevancy pruning/SinE    : 0
% 4.50/4.71  # Initial clauses                      : 25
% 4.50/4.71  # Removed in clause preprocessing      : 3
% 4.50/4.71  # Initial clauses in saturation        : 22
% 4.50/4.71  # Processed clauses                    : 3315
% 4.50/4.71  # ...of these trivial                  : 172
% 4.50/4.71  # ...subsumed                          : 1756
% 4.50/4.71  # ...remaining for further processing  : 1387
% 4.50/4.71  # Other redundant clauses eliminated   : 1203
% 4.50/4.71  # Clauses deleted for lack of memory   : 0
% 4.50/4.71  # Backward-subsumed                    : 146
% 4.50/4.71  # Backward-rewritten                   : 544
% 4.50/4.71  # Generated clauses                    : 232239
% 4.50/4.71  # ...of the previous two non-trivial   : 227527
% 4.50/4.71  # Contextual simplify-reflections      : 154
% 4.50/4.71  # Paramodulations                      : 229454
% 4.50/4.71  # Factorizations                       : 1522
% 4.50/4.71  # Equation resolutions                 : 1263
% 4.50/4.71  # Propositional unsat checks           : 0
% 4.50/4.71  #    Propositional check models        : 0
% 4.50/4.71  #    Propositional check unsatisfiable : 0
% 4.50/4.71  #    Propositional clauses             : 0
% 4.50/4.71  #    Propositional clauses after purity: 0
% 4.50/4.71  #    Propositional unsat core size     : 0
% 4.50/4.71  #    Propositional preprocessing time  : 0.000
% 4.50/4.71  #    Propositional encoding time       : 0.000
% 4.50/4.71  #    Propositional solver time         : 0.000
% 4.50/4.71  #    Success case prop preproc time    : 0.000
% 4.50/4.71  #    Success case prop encoding time   : 0.000
% 4.50/4.71  #    Success case prop solver time     : 0.000
% 4.50/4.71  # Current number of processed clauses  : 697
% 4.50/4.71  #    Positive orientable unit clauses  : 35
% 4.50/4.71  #    Positive unorientable unit clauses: 1
% 4.50/4.71  #    Negative unit clauses             : 2
% 4.50/4.71  #    Non-unit-clauses                  : 659
% 4.50/4.71  # Current number of unprocessed clauses: 223491
% 4.50/4.71  # ...number of literals in the above   : 1485042
% 4.50/4.71  # Current number of archived formulas  : 0
% 4.50/4.71  # Current number of archived clauses   : 693
% 4.50/4.71  # Clause-clause subsumption calls (NU) : 166424
% 4.50/4.71  # Rec. Clause-clause subsumption calls : 58100
% 4.50/4.71  # Non-unit clause-clause subsumptions  : 1866
% 4.50/4.71  # Unit Clause-clause subsumption calls : 2080
% 4.50/4.71  # Rewrite failures with RHS unbound    : 0
% 4.50/4.71  # BW rewrite match attempts            : 529
% 4.50/4.71  # BW rewrite match successes           : 45
% 4.50/4.71  # Condensation attempts                : 0
% 4.50/4.71  # Condensation successes               : 0
% 4.50/4.71  # Termbank termtop insertions          : 6644315
% 4.50/4.72  
% 4.50/4.72  # -------------------------------------------------
% 4.50/4.72  # User time                : 4.264 s
% 4.50/4.72  # System time              : 0.111 s
% 4.50/4.72  # Total time               : 4.375 s
% 4.50/4.72  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
