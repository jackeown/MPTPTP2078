%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : compts_1__t10_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:49 EDT 2019

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :  178 (2758 expanded)
%              Number of clauses        :  148 (1252 expanded)
%              Number of leaves         :   15 ( 700 expanded)
%              Depth                    :   22
%              Number of atoms          :  713 (11547 expanded)
%              Number of equality atoms :   23 ( 372 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   47 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_compts_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ~ ( m1_setfam_1(X3,X2)
                    & v1_tops_2(X3,X1)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                       => ~ ( r1_tarski(X4,X3)
                            & m1_setfam_1(X4,X2)
                            & v1_finset_1(X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',d7_compts_1)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',dt_k2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',dt_l1_pre_topc)).

fof(t10_compts_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_compts_1(X1)
      <=> v2_compts_1(k2_struct_0(X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',t10_compts_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',t2_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',t5_subset)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',d3_struct_0)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',existence_m1_subset_1)).

fof(d3_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_compts_1(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
                & v1_tops_2(X2,X1)
                & ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ~ ( r1_tarski(X3,X2)
                        & m1_setfam_1(X3,u1_struct_0(X1))
                        & v1_finset_1(X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',d3_compts_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',t3_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',t6_boole)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',t1_subset)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',t8_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',dt_o_0_0_xboole_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t10_compts_1.p',t4_subset)).

fof(c_0_15,plain,(
    ! [X14,X15,X16,X19] :
      ( ( m1_subset_1(esk4_3(X14,X15,X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ m1_setfam_1(X16,X15)
        | ~ v1_tops_2(X16,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ v2_compts_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( r1_tarski(esk4_3(X14,X15,X16),X16)
        | ~ m1_setfam_1(X16,X15)
        | ~ v1_tops_2(X16,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ v2_compts_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( m1_setfam_1(esk4_3(X14,X15,X16),X15)
        | ~ m1_setfam_1(X16,X15)
        | ~ v1_tops_2(X16,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ v2_compts_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( v1_finset_1(esk4_3(X14,X15,X16))
        | ~ m1_setfam_1(X16,X15)
        | ~ v1_tops_2(X16,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ v2_compts_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk5_2(X14,X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | v2_compts_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( m1_setfam_1(esk5_2(X14,X15),X15)
        | v2_compts_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( v1_tops_2(esk5_2(X14,X15),X14)
        | v2_compts_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r1_tarski(X19,esk5_2(X14,X15))
        | ~ m1_setfam_1(X19,X15)
        | ~ v1_finset_1(X19)
        | v2_compts_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_compts_1])])])])])).

fof(c_0_16,plain,(
    ! [X20] :
      ( ~ l1_struct_0(X20)
      | m1_subset_1(k2_struct_0(X20),k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

fof(c_0_17,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ( v1_compts_1(X1)
        <=> v2_compts_1(k2_struct_0(X1),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t10_compts_1])).

fof(c_0_19,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X30,X31)
      | v1_xboole_0(X31)
      | r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk5_2(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & ( ~ v1_compts_1(esk1_0)
      | ~ v2_compts_1(k2_struct_0(esk1_0),esk1_0) )
    & ( v1_compts_1(esk1_0)
      | v2_compts_1(k2_struct_0(esk1_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X37,X38,X39] :
      ( ~ r2_hidden(X37,X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(X39))
      | ~ v1_xboole_0(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk5_2(X1,k2_struct_0(X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_compts_1(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_2(esk1_0,k2_struct_0(esk1_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_31,plain,(
    ! [X13] :
      ( ~ l1_struct_0(X13)
      | k2_struct_0(X13) = u1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_32,plain,(
    ! [X26] : m1_subset_1(esk9_1(X26),X26) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_33,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

fof(c_0_34,plain,(
    ! [X8,X9,X12] :
      ( ( m1_subset_1(esk2_2(X8,X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ m1_setfam_1(X9,u1_struct_0(X8))
        | ~ v1_tops_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ v1_compts_1(X8)
        | ~ l1_pre_topc(X8) )
      & ( r1_tarski(esk2_2(X8,X9),X9)
        | ~ m1_setfam_1(X9,u1_struct_0(X8))
        | ~ v1_tops_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ v1_compts_1(X8)
        | ~ l1_pre_topc(X8) )
      & ( m1_setfam_1(esk2_2(X8,X9),u1_struct_0(X8))
        | ~ m1_setfam_1(X9,u1_struct_0(X8))
        | ~ v1_tops_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ v1_compts_1(X8)
        | ~ l1_pre_topc(X8) )
      & ( v1_finset_1(esk2_2(X8,X9))
        | ~ m1_setfam_1(X9,u1_struct_0(X8))
        | ~ v1_tops_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ v1_compts_1(X8)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk3_1(X8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | v1_compts_1(X8)
        | ~ l1_pre_topc(X8) )
      & ( m1_setfam_1(esk3_1(X8),u1_struct_0(X8))
        | v1_compts_1(X8)
        | ~ l1_pre_topc(X8) )
      & ( v1_tops_2(esk3_1(X8),X8)
        | v1_compts_1(X8)
        | ~ l1_pre_topc(X8) )
      & ( ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ r1_tarski(X12,esk3_1(X8))
        | ~ m1_setfam_1(X12,u1_struct_0(X8))
        | ~ v1_finset_1(X12)
        | v1_compts_1(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_compts_1])])])])])).

fof(c_0_35,plain,(
    ! [X32,X33] :
      ( ( ~ m1_subset_1(X32,k1_zfmisc_1(X33))
        | r1_tarski(X32,X33) )
      & ( ~ r1_tarski(X32,X33)
        | m1_subset_1(X32,k1_zfmisc_1(X33)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_36,negated_conjecture,
    ( v2_compts_1(k2_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,esk5_2(esk1_0,k2_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk9_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_hidden(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_27])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(esk2_2(X1,X2),X2)
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( m1_setfam_1(esk5_2(X1,X2),X2)
    | v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_44,plain,(
    ! [X40] :
      ( ~ v1_xboole_0(X40)
      | X40 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_45,negated_conjecture,
    ( v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(X1,esk5_2(esk1_0,u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk9_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_38])).

fof(c_0_47,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | m1_subset_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_hidden(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk3_1(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | v1_compts_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_27])).

fof(c_0_50,plain,(
    ! [X43,X44] :
      ( ~ v1_xboole_0(X43)
      | X43 = X44
      | ~ v1_xboole_0(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk9_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(X2))
    | ~ v1_tops_2(X2,X1)
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,plain,
    ( m1_setfam_1(esk5_2(X1,k2_struct_0(X1)),k2_struct_0(X1))
    | v2_compts_1(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_21]),c_0_22])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(esk5_2(esk1_0,u1_struct_0(esk1_0)))
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_hidden(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_22]),c_0_27])])).

cnf(c_0_59,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,esk3_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_49])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( v1_xboole_0(esk9_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_46])).

cnf(c_0_62,plain,
    ( ~ v1_xboole_0(X1)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_setfam_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r2_hidden(X3,esk2_2(X2,X1))
    | ~ v1_compts_1(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( m1_setfam_1(esk5_2(esk1_0,k2_struct_0(esk1_0)),k2_struct_0(esk1_0))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_27])).

cnf(c_0_64,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(esk5_2(esk1_0,u1_struct_0(esk1_0)))
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_22]),c_0_27])])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(esk3_1(esk1_0))
    | v1_compts_1(esk1_0)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_46])).

cnf(c_0_68,plain,
    ( X1 = esk9_1(k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,plain,
    ( v1_xboole_0(esk2_2(X1,X2))
    | ~ v1_xboole_0(X2)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_46])).

cnf(c_0_70,plain,
    ( v1_tops_2(esk5_2(X1,X2),X1)
    | v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_compts_1(esk1_0)
    | ~ v2_compts_1(k2_struct_0(esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_72,negated_conjecture,
    ( m1_setfam_1(esk5_2(esk1_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0))
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_37])).

cnf(c_0_73,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_54,c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(esk5_2(esk1_0,u1_struct_0(esk1_0)))
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( m1_setfam_1(esk3_1(X1),u1_struct_0(X1))
    | v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_76,negated_conjecture,
    ( v1_xboole_0(esk3_1(esk1_0))
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_compts_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_66])).

cnf(c_0_77,plain,
    ( v1_finset_1(esk2_2(X1,X2))
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_78,plain,
    ( esk2_2(X1,X2) = esk9_1(k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3)
    | ~ v1_xboole_0(X2)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_79,plain,
    ( v1_tops_2(esk5_2(X1,k2_struct_0(X1)),X1)
    | v2_compts_1(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_21]),c_0_22])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(esk5_2(esk1_0,k2_struct_0(esk1_0)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_46])).

cnf(c_0_81,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_37])).

cnf(c_0_82,negated_conjecture,
    ( m1_setfam_1(esk5_2(esk1_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0))
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_22]),c_0_27])])).

cnf(c_0_83,negated_conjecture,
    ( esk5_2(esk1_0,u1_struct_0(esk1_0)) = o_0_0_xboole_0
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( m1_setfam_1(esk3_1(esk1_0),u1_struct_0(esk1_0))
    | v1_compts_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_27])).

cnf(c_0_85,negated_conjecture,
    ( esk3_1(esk1_0) = o_0_0_xboole_0
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_compts_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_76])).

cnf(c_0_86,plain,
    ( r1_tarski(esk4_3(X1,X2,X3),X3)
    | ~ m1_setfam_1(X3,X2)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_87,plain,(
    ! [X34,X35,X36] :
      ( ~ r2_hidden(X34,X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(X36))
      | m1_subset_1(X34,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_88,plain,
    ( v1_finset_1(esk9_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ v1_tops_2(X2,X3)
    | ~ m1_setfam_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ v1_compts_1(X3)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_89,negated_conjecture,
    ( v1_compts_1(esk1_0)
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_90,negated_conjecture,
    ( v1_tops_2(esk5_2(esk1_0,k2_struct_0(esk1_0)),esk1_0)
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_27])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(esk5_2(esk1_0,k2_struct_0(esk1_0)))
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_66])).

cnf(c_0_92,negated_conjecture,
    ( ~ v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v1_compts_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_22]),c_0_27])])).

cnf(c_0_93,negated_conjecture,
    ( m1_setfam_1(o_0_0_xboole_0,u1_struct_0(esk1_0))
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_94,negated_conjecture,
    ( m1_setfam_1(o_0_0_xboole_0,u1_struct_0(esk1_0))
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_compts_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_95,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(X3))
    | ~ v1_tops_2(X3,X1)
    | ~ m1_setfam_1(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_86])).

cnf(c_0_96,plain,
    ( esk9_1(k1_zfmisc_1(X1)) = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_61])).

cnf(c_0_97,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_98,negated_conjecture,
    ( v1_finset_1(esk9_1(k1_zfmisc_1(X1)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(esk5_2(esk1_0,k2_struct_0(esk1_0)))
    | ~ v1_xboole_0(X1)
    | ~ m1_setfam_1(esk5_2(esk1_0,k2_struct_0(esk1_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_30]),c_0_27])]),c_0_89]),c_0_90])).

cnf(c_0_99,negated_conjecture,
    ( esk5_2(esk1_0,k2_struct_0(esk1_0)) = o_0_0_xboole_0
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_91])).

cnf(c_0_100,negated_conjecture,
    ( m1_setfam_1(o_0_0_xboole_0,u1_struct_0(esk1_0))
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_101,plain,
    ( ~ v1_xboole_0(X1)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_setfam_1(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X4,esk4_3(X2,X3,X1))
    | ~ v2_compts_1(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_95])).

cnf(c_0_102,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_96])).

cnf(c_0_103,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,esk9_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_38])).

cnf(c_0_104,plain,
    ( v2_compts_1(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,esk5_2(X2,X3))
    | ~ m1_setfam_1(X1,X3)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_105,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_106,plain,
    ( esk9_1(k1_zfmisc_1(X1)) = esk9_1(k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_61])).

cnf(c_0_107,negated_conjecture,
    ( v1_finset_1(esk9_1(k1_zfmisc_1(X1)))
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_55])]),c_0_100])).

cnf(c_0_108,negated_conjecture,
    ( esk5_2(esk1_0,k2_struct_0(esk1_0)) = esk9_1(k1_zfmisc_1(X1))
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_91])).

cnf(c_0_109,plain,
    ( v1_xboole_0(esk4_3(X1,X2,X3))
    | ~ v1_xboole_0(X3)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_setfam_1(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_46])).

cnf(c_0_110,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_55])).

cnf(c_0_111,plain,
    ( v1_xboole_0(esk9_1(k1_zfmisc_1(X1)))
    | m1_subset_1(esk9_1(esk9_1(k1_zfmisc_1(X1))),X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_46])).

cnf(c_0_112,plain,
    ( esk2_2(X1,X2) = o_0_0_xboole_0
    | ~ v1_xboole_0(X2)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_69])).

cnf(c_0_113,plain,
    ( v2_compts_1(X1,X2)
    | ~ v1_finset_1(X3)
    | ~ m1_setfam_1(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk5_2(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_114,plain,
    ( m1_subset_1(esk9_1(k1_zfmisc_1(X1)),k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_106])).

cnf(c_0_115,negated_conjecture,
    ( v1_finset_1(esk9_1(k1_zfmisc_1(esk5_2(esk1_0,k2_struct_0(esk1_0)))))
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_91])).

cnf(c_0_116,negated_conjecture,
    ( esk9_1(k1_zfmisc_1(esk5_2(esk1_0,k2_struct_0(esk1_0)))) = esk5_2(esk1_0,k2_struct_0(esk1_0))
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_91])).

cnf(c_0_117,plain,
    ( m1_setfam_1(esk2_2(X1,X2),u1_struct_0(X1))
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_118,plain,
    ( v1_finset_1(esk4_3(X1,X2,X3))
    | ~ m1_setfam_1(X3,X2)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_119,plain,
    ( esk4_3(X1,X2,X3) = o_0_0_xboole_0
    | ~ v1_xboole_0(X3)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_setfam_1(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_109])).

cnf(c_0_120,plain,
    ( ~ r2_hidden(X1,o_0_0_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_110]),c_0_55])])).

cnf(c_0_121,plain,
    ( v1_xboole_0(esk9_1(k1_zfmisc_1(X1)))
    | r2_hidden(esk9_1(esk9_1(k1_zfmisc_1(X1))),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_111]),c_0_61])).

cnf(c_0_122,plain,
    ( v1_finset_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(X1)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_setfam_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ v1_compts_1(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_112])).

cnf(c_0_123,plain,
    ( v2_compts_1(X1,X2)
    | ~ v1_xboole_0(esk5_2(X2,X1))
    | ~ v1_xboole_0(X3)
    | ~ v1_finset_1(esk9_1(k1_zfmisc_1(X3)))
    | ~ m1_setfam_1(esk9_1(k1_zfmisc_1(X3)),X1)
    | ~ m1_subset_1(esk9_1(k1_zfmisc_1(X3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_124,negated_conjecture,
    ( v1_finset_1(esk5_2(esk1_0,k2_struct_0(esk1_0)))
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_125,plain,
    ( m1_setfam_1(o_0_0_xboole_0,u1_struct_0(X1))
    | ~ v1_xboole_0(X2)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_117,c_0_112])).

cnf(c_0_126,plain,
    ( v1_finset_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(X1)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_setfam_1(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_compts_1(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_127,plain,
    ( v1_xboole_0(esk9_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_128,negated_conjecture,
    ( v1_finset_1(o_0_0_xboole_0)
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(esk5_2(esk1_0,k2_struct_0(esk1_0)))
    | ~ m1_setfam_1(esk5_2(esk1_0,k2_struct_0(esk1_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_30]),c_0_27])]),c_0_89]),c_0_90])).

cnf(c_0_129,plain,
    ( v1_tops_2(esk3_1(X1),X1)
    | v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_130,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_37])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0)
    | v2_compts_1(X1,X2)
    | ~ v1_xboole_0(esk5_2(X2,X1))
    | ~ m1_setfam_1(esk5_2(esk1_0,k2_struct_0(esk1_0)),X1)
    | ~ m1_subset_1(esk5_2(esk1_0,k2_struct_0(esk1_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_116]),c_0_124]),c_0_91])).

cnf(c_0_132,negated_conjecture,
    ( m1_setfam_1(o_0_0_xboole_0,u1_struct_0(esk1_0))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(esk5_2(esk1_0,k2_struct_0(esk1_0)))
    | ~ m1_setfam_1(esk5_2(esk1_0,k2_struct_0(esk1_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_30]),c_0_27])]),c_0_89]),c_0_90])).

cnf(c_0_133,plain,
    ( v1_finset_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2)
    | ~ v1_tops_2(esk9_1(k1_zfmisc_1(X2)),X1)
    | ~ m1_setfam_1(esk9_1(k1_zfmisc_1(X2)),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_compts_1(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_114]),c_0_61])).

cnf(c_0_134,plain,
    ( esk9_1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_127])).

cnf(c_0_135,negated_conjecture,
    ( v1_finset_1(o_0_0_xboole_0)
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(esk5_2(esk1_0,u1_struct_0(esk1_0)))
    | ~ l1_struct_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_37]),c_0_82])).

cnf(c_0_136,negated_conjecture,
    ( v1_tops_2(esk3_1(esk1_0),esk1_0)
    | v1_compts_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_27])).

cnf(c_0_137,plain,
    ( v2_compts_1(X1,X2)
    | ~ v1_tops_2(esk5_2(X2,X1),X3)
    | ~ m1_setfam_1(esk2_2(X3,esk5_2(X2,X1)),X1)
    | ~ m1_setfam_1(esk5_2(X2,X1),u1_struct_0(X3))
    | ~ m1_subset_1(esk2_2(X3,esk5_2(X2,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(esk5_2(X2,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_compts_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_42]),c_0_77])).

cnf(c_0_138,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_139,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_130,c_0_22])).

cnf(c_0_140,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0)
    | v2_compts_1(X1,esk1_0)
    | ~ v1_xboole_0(esk5_2(esk1_0,X1))
    | ~ m1_setfam_1(esk5_2(esk1_0,k2_struct_0(esk1_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_30]),c_0_27])])).

cnf(c_0_141,negated_conjecture,
    ( m1_setfam_1(o_0_0_xboole_0,u1_struct_0(esk1_0))
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(esk5_2(esk1_0,u1_struct_0(esk1_0)))
    | ~ l1_struct_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_37]),c_0_82])).

cnf(c_0_142,plain,
    ( v1_compts_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,esk3_1(X2))
    | ~ m1_setfam_1(X1,u1_struct_0(X2))
    | ~ v1_finset_1(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_143,plain,
    ( v1_finset_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_2(o_0_0_xboole_0,X1)
    | ~ m1_setfam_1(o_0_0_xboole_0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_55])])).

cnf(c_0_144,negated_conjecture,
    ( v1_finset_1(o_0_0_xboole_0)
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(esk5_2(esk1_0,u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_22]),c_0_27])])).

cnf(c_0_145,negated_conjecture,
    ( v1_tops_2(o_0_0_xboole_0,esk1_0)
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_99])).

cnf(c_0_146,negated_conjecture,
    ( v1_tops_2(o_0_0_xboole_0,esk1_0)
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_compts_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_85])).

cnf(c_0_147,plain,
    ( v2_compts_1(X1,X2)
    | ~ m1_setfam_1(esk2_2(X2,esk5_2(X2,X1)),X1)
    | ~ m1_setfam_1(esk5_2(X2,X1),u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_compts_1(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_20]),c_0_70])).

cnf(c_0_148,plain,
    ( m1_subset_1(esk5_2(X1,u1_struct_0(X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_compts_1(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_139])).

cnf(c_0_149,plain,
    ( m1_setfam_1(esk5_2(X1,u1_struct_0(X1)),u1_struct_0(X1))
    | v2_compts_1(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_139])).

cnf(c_0_150,plain,
    ( v1_tops_2(esk5_2(X1,u1_struct_0(X1)),X1)
    | v2_compts_1(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_139])).

cnf(c_0_151,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0)
    | v2_compts_1(X1,esk1_0)
    | ~ v1_xboole_0(esk5_2(esk1_0,X1))
    | ~ m1_setfam_1(o_0_0_xboole_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_140,c_0_99])).

cnf(c_0_152,negated_conjecture,
    ( m1_setfam_1(o_0_0_xboole_0,u1_struct_0(esk1_0))
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v1_xboole_0(esk5_2(esk1_0,u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_22]),c_0_27])])).

cnf(c_0_153,negated_conjecture,
    ( v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | v1_compts_1(esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_37])).

cnf(c_0_154,plain,
    ( v1_compts_1(X1)
    | ~ v1_finset_1(X2)
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_1(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_142,c_0_105])).

cnf(c_0_155,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(esk3_1(esk1_0)))
    | v1_compts_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_76])).

cnf(c_0_156,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_66])).

cnf(c_0_157,plain,
    ( v1_finset_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_2(o_0_0_xboole_0,X1)
    | ~ m1_setfam_1(o_0_0_xboole_0,u1_struct_0(X1))
    | ~ v2_compts_1(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_143,c_0_139])).

cnf(c_0_158,negated_conjecture,
    ( v1_finset_1(o_0_0_xboole_0)
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_83]),c_0_55])])).

cnf(c_0_159,negated_conjecture,
    ( v1_tops_2(o_0_0_xboole_0,esk1_0)
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_145]),c_0_146])).

cnf(c_0_160,plain,
    ( v1_compts_1(X1)
    | ~ v1_tops_2(esk3_1(X1),X2)
    | ~ m1_setfam_1(esk4_3(X2,X3,esk3_1(X1)),u1_struct_0(X1))
    | ~ m1_setfam_1(esk3_1(X1),X3)
    | ~ m1_subset_1(esk4_3(X2,X3,esk3_1(X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(esk3_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_compts_1(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_86]),c_0_118])).

cnf(c_0_161,plain,
    ( m1_setfam_1(esk4_3(X1,X2,X3),X2)
    | ~ m1_setfam_1(X3,X2)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_162,plain,
    ( v2_compts_1(u1_struct_0(X1),X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_117]),c_0_139]),c_0_148]),c_0_149]),c_0_150])).

cnf(c_0_163,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | v2_compts_1(k2_struct_0(esk1_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_139]),c_0_27])]),c_0_152]),c_0_74])).

cnf(c_0_164,negated_conjecture,
    ( v2_compts_1(u1_struct_0(esk1_0),esk1_0)
    | v1_compts_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_22]),c_0_27])])).

cnf(c_0_165,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_compts_1(esk1_0)
    | ~ v1_finset_1(o_0_0_xboole_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_27])]),c_0_156]),c_0_100])).

cnf(c_0_166,negated_conjecture,
    ( v1_finset_1(o_0_0_xboole_0)
    | m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_66]),c_0_27])]),c_0_158]),c_0_100]),c_0_159])).

cnf(c_0_167,plain,
    ( v1_compts_1(X1)
    | ~ v1_tops_2(esk3_1(X1),X2)
    | ~ m1_subset_1(esk4_3(X2,u1_struct_0(X1),esk3_1(X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(esk3_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_compts_1(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_75])).

cnf(c_0_168,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X3,X2)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_169,negated_conjecture,
    ( ~ v1_compts_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_162]),c_0_27])])).

cnf(c_0_170,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v2_compts_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_163]),c_0_164])).

cnf(c_0_171,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_compts_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_165,c_0_166])).

cnf(c_0_172,plain,
    ( v1_compts_1(X1)
    | ~ v1_tops_2(esk3_1(X1),X1)
    | ~ m1_subset_1(esk3_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_compts_1(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_setfam_1(esk3_1(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_167,c_0_168])).

cnf(c_0_173,negated_conjecture,
    ( m1_setfam_1(esk3_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_84,c_0_169])).

cnf(c_0_174,negated_conjecture,
    ( v1_tops_2(esk3_1(esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[c_0_136,c_0_169])).

cnf(c_0_175,negated_conjecture,
    ( v2_compts_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[c_0_164,c_0_169])).

cnf(c_0_176,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_170]),c_0_171])).

cnf(c_0_177,plain,
    ( $false ),
    inference(cdclpropres,[status(thm)],[c_0_172,c_0_40,c_0_169,c_0_173,c_0_174,c_0_175,c_0_176,c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
