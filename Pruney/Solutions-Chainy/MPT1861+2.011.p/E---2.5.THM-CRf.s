%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:36 EST 2020

% Result     : Theorem 0.81s
% Output     : CNFRefutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 507 expanded)
%              Number of clauses        :   62 ( 240 expanded)
%              Number of leaves         :    9 ( 126 expanded)
%              Depth                    :   26
%              Number of atoms          :  214 (1444 expanded)
%              Number of equality atoms :   44 ( 378 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t29_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v2_tex_2(X2,X1)
                  | v2_tex_2(X3,X1) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r1_tarski(X3,X2)
                  & v2_tex_2(X2,X1) )
               => v2_tex_2(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_9,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X27,X28] : k1_setfam_1(k2_tarski(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v2_tex_2(X2,X1)
                    | v2_tex_2(X3,X1) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tex_2])).

fof(c_0_14,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_15,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X29,k1_zfmisc_1(X30))
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | m1_subset_1(X29,k1_zfmisc_1(X30)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( v2_tex_2(esk4_0,esk3_0)
      | v2_tex_2(esk5_0,esk3_0) )
    & ~ v2_tex_2(k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_18,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X24))
      | k9_subset_1(X24,X25,X26) = k3_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,esk5_0)) = esk5_0
    | r2_hidden(esk2_3(X1,esk5_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_28,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_29,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( k9_subset_1(X1,X2,esk5_0) = esk5_0
    | r2_hidden(esk2_3(X2,esk5_0,esk5_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( k9_subset_1(X1,X2,esk5_0) = esk5_0
    | r2_hidden(esk2_3(X2,esk5_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_12]),c_0_12])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_20]),c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( k9_subset_1(esk5_0,X1,esk5_0) = esk5_0
    | r2_hidden(esk2_3(X1,esk5_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( k9_subset_1(X1,X2,X3) = k1_setfam_1(k2_tarski(X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( k9_subset_1(esk5_0,u1_struct_0(esk3_0),esk5_0) = esk5_0
    | k1_setfam_1(k2_tarski(esk5_0,u1_struct_0(esk3_0))) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( k9_subset_1(esk5_0,u1_struct_0(esk3_0),esk5_0) = esk5_0
    | k9_subset_1(X1,u1_struct_0(esk3_0),esk5_0) = esk5_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_45,negated_conjecture,
    ( k9_subset_1(esk5_0,u1_struct_0(esk3_0),esk5_0) = esk5_0
    | k9_subset_1(X1,u1_struct_0(esk3_0),esk5_0) = esk5_0
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_31])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_44,c_0_12])).

cnf(c_0_47,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

cnf(c_0_48,negated_conjecture,
    ( k9_subset_1(esk5_0,u1_struct_0(esk3_0),esk5_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k9_subset_1(X1,u1_struct_0(esk3_0),esk5_0) = esk5_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_51,plain,(
    ! [X31,X32,X33] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ r1_tarski(X33,X32)
      | ~ v2_tex_2(X32,X31)
      | v2_tex_2(X33,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_tex_2])])])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,X2)),X3),X2)
    | r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk5_0,u1_struct_0(esk3_0))) = esk5_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_50]),c_0_38])).

fof(c_0_54,plain,(
    ! [X22,X23] : r1_tarski(k3_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_55,plain,
    ( v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))),X4),X3)
    | r1_tarski(k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))),X4) ),
    inference(spm,[status(thm)],[c_0_49,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk5_0,u1_struct_0(esk3_0))) = esk5_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_31]),c_0_37])])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_60,plain,
    ( v2_tex_2(X1,X2)
    | ~ v2_tex_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,u1_struct_0(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))),X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk5_0,u1_struct_0(esk3_0))) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_22])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_12])).

cnf(c_0_65,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(X1,esk4_0,esk5_0),esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_47]),c_0_22])])).

cnf(c_0_66,negated_conjecture,
    ( v2_tex_2(X1,esk3_0)
    | ~ v2_tex_2(esk5_0,esk3_0)
    | ~ r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_22]),c_0_61])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,esk5_0)),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_38])).

cnf(c_0_69,negated_conjecture,
    ( ~ v2_tex_2(k1_setfam_1(k2_tarski(esk4_0,esk5_0)),esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_26])).

cnf(c_0_70,negated_conjecture,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X1,esk5_0)),esk3_0)
    | ~ v2_tex_2(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_73,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0)
    | v2_tex_2(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_22])).

cnf(c_0_75,negated_conjecture,
    ( v2_tex_2(X1,esk3_0)
    | ~ v2_tex_2(esk4_0,esk3_0)
    | ~ r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_72]),c_0_61])])).

cnf(c_0_76,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( v2_tex_2(X1,esk3_0)
    | ~ r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_78,negated_conjecture,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X1,esk5_0)),esk3_0)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X1,esk5_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_78]),c_0_64])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_22,c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:59:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.81/1.02  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.81/1.02  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.81/1.02  #
% 0.81/1.02  # Preprocessing time       : 0.028 s
% 0.81/1.02  # Presaturation interreduction done
% 0.81/1.02  
% 0.81/1.02  # Proof found!
% 0.81/1.02  # SZS status Theorem
% 0.81/1.02  # SZS output start CNFRefutation
% 0.81/1.02  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.81/1.02  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.81/1.02  fof(t29_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X2,X1)|v2_tex_2(X3,X1))=>v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 0.81/1.02  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.81/1.02  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.81/1.02  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.81/1.02  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.81/1.02  fof(t28_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v2_tex_2(X2,X1))=>v2_tex_2(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 0.81/1.02  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.81/1.02  fof(c_0_9, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14))&(r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k3_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k3_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))&(r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.81/1.02  fof(c_0_10, plain, ![X27, X28]:k1_setfam_1(k2_tarski(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.81/1.02  cnf(c_0_11, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.81/1.02  cnf(c_0_12, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.81/1.02  fof(c_0_13, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X2,X1)|v2_tex_2(X3,X1))=>v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t29_tex_2])).
% 0.81/1.02  fof(c_0_14, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.81/1.02  cnf(c_0_15, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.81/1.02  fof(c_0_16, plain, ![X29, X30]:((~m1_subset_1(X29,k1_zfmisc_1(X30))|r1_tarski(X29,X30))&(~r1_tarski(X29,X30)|m1_subset_1(X29,k1_zfmisc_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.81/1.02  fof(c_0_17, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((v2_tex_2(esk4_0,esk3_0)|v2_tex_2(esk5_0,esk3_0))&~v2_tex_2(k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.81/1.02  fof(c_0_18, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(X24))|k9_subset_1(X24,X25,X26)=k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.81/1.02  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.81/1.02  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_15])).
% 0.81/1.02  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.81/1.02  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.81/1.02  cnf(c_0_23, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.81/1.02  cnf(c_0_24, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk2_3(X1,X2,X2),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.81/1.02  cnf(c_0_25, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.81/1.02  cnf(c_0_26, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_23, c_0_12])).
% 0.81/1.02  cnf(c_0_27, negated_conjecture, (k1_setfam_1(k2_tarski(X1,esk5_0))=esk5_0|r2_hidden(esk2_3(X1,esk5_0,esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.81/1.02  fof(c_0_28, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.81/1.02  cnf(c_0_29, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.81/1.02  cnf(c_0_30, negated_conjecture, (k9_subset_1(X1,X2,esk5_0)=esk5_0|r2_hidden(esk2_3(X2,esk5_0,esk5_0),u1_struct_0(esk3_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.81/1.02  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.81/1.02  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.81/1.02  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.81/1.02  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.81/1.02  cnf(c_0_35, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_29, c_0_12])).
% 0.81/1.02  cnf(c_0_36, negated_conjecture, (k9_subset_1(X1,X2,esk5_0)=esk5_0|r2_hidden(esk2_3(X2,esk5_0,esk5_0),u1_struct_0(esk3_0))|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.81/1.02  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.81/1.02  cnf(c_0_38, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_12]), c_0_12])).
% 0.81/1.02  cnf(c_0_39, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_20]), c_0_20])).
% 0.81/1.02  cnf(c_0_40, negated_conjecture, (k9_subset_1(esk5_0,X1,esk5_0)=esk5_0|r2_hidden(esk2_3(X1,esk5_0,esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.81/1.02  cnf(c_0_41, plain, (k9_subset_1(X1,X2,X3)=k1_setfam_1(k2_tarski(X3,X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_26])).
% 0.81/1.02  cnf(c_0_42, negated_conjecture, (k9_subset_1(esk5_0,u1_struct_0(esk3_0),esk5_0)=esk5_0|k1_setfam_1(k2_tarski(esk5_0,u1_struct_0(esk3_0)))=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_38])).
% 0.81/1.02  cnf(c_0_43, negated_conjecture, (k9_subset_1(esk5_0,u1_struct_0(esk3_0),esk5_0)=esk5_0|k9_subset_1(X1,u1_struct_0(esk3_0),esk5_0)=esk5_0|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.81/1.02  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.81/1.02  cnf(c_0_45, negated_conjecture, (k9_subset_1(esk5_0,u1_struct_0(esk3_0),esk5_0)=esk5_0|k9_subset_1(X1,u1_struct_0(esk3_0),esk5_0)=esk5_0|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_31])).
% 0.81/1.02  cnf(c_0_46, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_44, c_0_12])).
% 0.81/1.02  cnf(c_0_47, plain, (k9_subset_1(X1,X2,X3)=k9_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_26, c_0_26])).
% 0.81/1.02  cnf(c_0_48, negated_conjecture, (k9_subset_1(esk5_0,u1_struct_0(esk3_0),esk5_0)=esk5_0), inference(spm,[status(thm)],[c_0_45, c_0_37])).
% 0.81/1.02  cnf(c_0_49, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2)))), inference(er,[status(thm)],[c_0_46])).
% 0.81/1.02  cnf(c_0_50, negated_conjecture, (k9_subset_1(X1,u1_struct_0(esk3_0),esk5_0)=esk5_0|~m1_subset_1(esk5_0,k1_zfmisc_1(esk5_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.81/1.02  fof(c_0_51, plain, ![X31, X32, X33]:(~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|(~r1_tarski(X33,X32)|~v2_tex_2(X32,X31)|v2_tex_2(X33,X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_tex_2])])])).
% 0.81/1.02  cnf(c_0_52, plain, (r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,X2)),X3),X2)|r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_49, c_0_33])).
% 0.81/1.02  cnf(c_0_53, negated_conjecture, (k1_setfam_1(k2_tarski(esk5_0,u1_struct_0(esk3_0)))=esk5_0|~m1_subset_1(esk5_0,k1_zfmisc_1(esk5_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_50]), c_0_38])).
% 0.81/1.02  fof(c_0_54, plain, ![X22, X23]:r1_tarski(k3_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.81/1.02  cnf(c_0_55, plain, (v2_tex_2(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~v2_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.81/1.02  cnf(c_0_56, plain, (r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))),X4),X3)|r1_tarski(k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))),X4)), inference(spm,[status(thm)],[c_0_49, c_0_52])).
% 0.81/1.02  cnf(c_0_57, negated_conjecture, (k1_setfam_1(k2_tarski(esk5_0,u1_struct_0(esk3_0)))=esk5_0|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_31]), c_0_37])])).
% 0.81/1.02  cnf(c_0_58, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.81/1.02  cnf(c_0_59, negated_conjecture, (~v2_tex_2(k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.81/1.02  cnf(c_0_60, plain, (v2_tex_2(X1,X2)|~v2_tex_2(X3,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,u1_struct_0(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_55, c_0_31])).
% 0.81/1.02  cnf(c_0_61, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.81/1.02  cnf(c_0_62, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))),X3)), inference(spm,[status(thm)],[c_0_32, c_0_56])).
% 0.81/1.02  cnf(c_0_63, negated_conjecture, (k1_setfam_1(k2_tarski(esk5_0,u1_struct_0(esk3_0)))=esk5_0), inference(spm,[status(thm)],[c_0_57, c_0_22])).
% 0.81/1.02  cnf(c_0_64, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_58, c_0_12])).
% 0.81/1.02  cnf(c_0_65, negated_conjecture, (~v2_tex_2(k9_subset_1(X1,esk4_0,esk5_0),esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_47]), c_0_22])])).
% 0.81/1.02  cnf(c_0_66, negated_conjecture, (v2_tex_2(X1,esk3_0)|~v2_tex_2(esk5_0,esk3_0)|~r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_22]), c_0_61])])).
% 0.81/1.02  cnf(c_0_67, negated_conjecture, (r1_tarski(k1_setfam_1(k2_tarski(X1,esk5_0)),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.81/1.02  cnf(c_0_68, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_64, c_0_38])).
% 0.81/1.02  cnf(c_0_69, negated_conjecture, (~v2_tex_2(k1_setfam_1(k2_tarski(esk4_0,esk5_0)),esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_65, c_0_26])).
% 0.81/1.02  cnf(c_0_70, negated_conjecture, (v2_tex_2(k1_setfam_1(k2_tarski(X1,esk5_0)),esk3_0)|~v2_tex_2(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])])).
% 0.81/1.02  cnf(c_0_71, negated_conjecture, (~v2_tex_2(esk5_0,esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.81/1.02  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.81/1.02  cnf(c_0_73, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)|v2_tex_2(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.81/1.02  cnf(c_0_74, negated_conjecture, (~v2_tex_2(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_71, c_0_22])).
% 0.81/1.02  cnf(c_0_75, negated_conjecture, (v2_tex_2(X1,esk3_0)|~v2_tex_2(esk4_0,esk3_0)|~r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_72]), c_0_61])])).
% 0.81/1.02  cnf(c_0_76, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)), inference(sr,[status(thm)],[c_0_73, c_0_74])).
% 0.81/1.02  cnf(c_0_77, negated_conjecture, (v2_tex_2(X1,esk3_0)|~r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])])).
% 0.81/1.02  cnf(c_0_78, negated_conjecture, (v2_tex_2(k1_setfam_1(k2_tarski(X1,esk5_0)),esk3_0)|~r1_tarski(k1_setfam_1(k2_tarski(X1,esk5_0)),esk4_0)), inference(spm,[status(thm)],[c_0_77, c_0_67])).
% 0.81/1.02  cnf(c_0_79, negated_conjecture, (~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_78]), c_0_64])])).
% 0.81/1.02  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_22, c_0_79]), ['proof']).
% 0.81/1.02  # SZS output end CNFRefutation
% 0.81/1.02  # Proof object total steps             : 81
% 0.81/1.02  # Proof object clause steps            : 62
% 0.81/1.02  # Proof object formula steps           : 19
% 0.81/1.02  # Proof object conjectures             : 34
% 0.81/1.02  # Proof object clause conjectures      : 31
% 0.81/1.02  # Proof object formula conjectures     : 3
% 0.81/1.02  # Proof object initial clauses used    : 18
% 0.81/1.02  # Proof object initial formulas used   : 9
% 0.81/1.02  # Proof object generating inferences   : 34
% 0.81/1.02  # Proof object simplifying inferences  : 27
% 0.81/1.02  # Training examples: 0 positive, 0 negative
% 0.81/1.02  # Parsed axioms                        : 9
% 0.81/1.02  # Removed by relevancy pruning/SinE    : 0
% 0.81/1.02  # Initial clauses                      : 21
% 0.81/1.02  # Removed in clause preprocessing      : 1
% 0.81/1.02  # Initial clauses in saturation        : 20
% 0.81/1.02  # Processed clauses                    : 3871
% 0.81/1.02  # ...of these trivial                  : 37
% 0.81/1.02  # ...subsumed                          : 2848
% 0.81/1.02  # ...remaining for further processing  : 986
% 0.81/1.02  # Other redundant clauses eliminated   : 3
% 0.81/1.02  # Clauses deleted for lack of memory   : 0
% 0.81/1.02  # Backward-subsumed                    : 82
% 0.81/1.02  # Backward-rewritten                   : 260
% 0.81/1.02  # Generated clauses                    : 41559
% 0.81/1.02  # ...of the previous two non-trivial   : 39513
% 0.81/1.02  # Contextual simplify-reflections      : 25
% 0.81/1.02  # Paramodulations                      : 41352
% 0.81/1.02  # Factorizations                       : 202
% 0.81/1.02  # Equation resolutions                 : 3
% 0.81/1.02  # Propositional unsat checks           : 0
% 0.81/1.02  #    Propositional check models        : 0
% 0.81/1.02  #    Propositional check unsatisfiable : 0
% 0.81/1.02  #    Propositional clauses             : 0
% 0.81/1.02  #    Propositional clauses after purity: 0
% 0.81/1.02  #    Propositional unsat core size     : 0
% 0.81/1.02  #    Propositional preprocessing time  : 0.000
% 0.81/1.02  #    Propositional encoding time       : 0.000
% 0.81/1.02  #    Propositional solver time         : 0.000
% 0.81/1.02  #    Success case prop preproc time    : 0.000
% 0.81/1.02  #    Success case prop encoding time   : 0.000
% 0.81/1.02  #    Success case prop solver time     : 0.000
% 0.81/1.02  # Current number of processed clauses  : 619
% 0.81/1.02  #    Positive orientable unit clauses  : 61
% 0.81/1.02  #    Positive unorientable unit clauses: 1
% 0.81/1.02  #    Negative unit clauses             : 16
% 0.81/1.02  #    Non-unit-clauses                  : 541
% 0.81/1.02  # Current number of unprocessed clauses: 35401
% 0.81/1.02  # ...number of literals in the above   : 193382
% 0.81/1.02  # Current number of archived formulas  : 0
% 0.81/1.02  # Current number of archived clauses   : 365
% 0.81/1.02  # Clause-clause subsumption calls (NU) : 99565
% 0.81/1.02  # Rec. Clause-clause subsumption calls : 63880
% 0.81/1.02  # Non-unit clause-clause subsumptions  : 2083
% 0.81/1.02  # Unit Clause-clause subsumption calls : 4620
% 0.81/1.02  # Rewrite failures with RHS unbound    : 0
% 0.81/1.02  # BW rewrite match attempts            : 693
% 0.81/1.02  # BW rewrite match successes           : 34
% 0.81/1.02  # Condensation attempts                : 0
% 0.81/1.02  # Condensation successes               : 0
% 0.81/1.02  # Termbank termtop insertions          : 949629
% 0.81/1.02  
% 0.81/1.02  # -------------------------------------------------
% 0.81/1.02  # User time                : 0.655 s
% 0.81/1.02  # System time              : 0.023 s
% 0.81/1.02  # Total time               : 0.678 s
% 0.81/1.02  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
