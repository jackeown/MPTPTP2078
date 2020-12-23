%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t58_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:54 EDT 2019

% Result     : Theorem 42.10s
% Output     : CNFRefutation 42.18s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 635 expanded)
%              Number of clauses        :   35 ( 206 expanded)
%              Number of leaves         :   10 ( 156 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 (4217 expanded)
%              Number of equality atoms :   26 ( 433 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,X2)
                 => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) = k6_domain_1(u1_struct_0(X1),X3) ) )
           => v2_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t58_tex_2.p',t58_tex_2)).

fof(t57_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v4_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) )
           => v2_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t58_tex_2.p',t57_tex_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t58_tex_2.p',t5_subset)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t58_tex_2.p',redefinition_k9_subset_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t58_tex_2.p',commutativity_k9_subset_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t58_tex_2.p',redefinition_k6_domain_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t58_tex_2.p',dt_k6_domain_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t58_tex_2.p',commutativity_k3_xboole_0)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t58_tex_2.p',dt_k2_pre_topc)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t58_tex_2.p',fc1_tops_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( r2_hidden(X3,X2)
                   => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) = k6_domain_1(u1_struct_0(X1),X3) ) )
             => v2_tex_2(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_tex_2])).

fof(c_0_11,plain,(
    ! [X225,X226,X228] :
      ( ( m1_subset_1(esk45_2(X225,X226),u1_struct_0(X225))
        | v2_tex_2(X226,X225)
        | ~ m1_subset_1(X226,k1_zfmisc_1(u1_struct_0(X225)))
        | v2_struct_0(X225)
        | ~ v2_pre_topc(X225)
        | ~ v3_tdlat_3(X225)
        | ~ l1_pre_topc(X225) )
      & ( r2_hidden(esk45_2(X225,X226),X226)
        | v2_tex_2(X226,X225)
        | ~ m1_subset_1(X226,k1_zfmisc_1(u1_struct_0(X225)))
        | v2_struct_0(X225)
        | ~ v2_pre_topc(X225)
        | ~ v3_tdlat_3(X225)
        | ~ l1_pre_topc(X225) )
      & ( ~ m1_subset_1(X228,k1_zfmisc_1(u1_struct_0(X225)))
        | ~ v4_pre_topc(X228,X225)
        | k9_subset_1(u1_struct_0(X225),X226,X228) != k6_domain_1(u1_struct_0(X225),esk45_2(X225,X226))
        | v2_tex_2(X226,X225)
        | ~ m1_subset_1(X226,k1_zfmisc_1(u1_struct_0(X225)))
        | v2_struct_0(X225)
        | ~ v2_pre_topc(X225)
        | ~ v3_tdlat_3(X225)
        | ~ l1_pre_topc(X225) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tex_2])])])])])])).

fof(c_0_12,negated_conjecture,(
    ! [X7] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & v3_tdlat_3(esk1_0)
      & l1_pre_topc(esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( ~ m1_subset_1(X7,u1_struct_0(esk1_0))
        | ~ r2_hidden(X7,esk2_0)
        | k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),X7))) = k6_domain_1(u1_struct_0(esk1_0),X7) )
      & ~ v2_tex_2(esk2_0,esk1_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

fof(c_0_13,plain,(
    ! [X229,X230,X231] :
      ( ~ r2_hidden(X229,X230)
      | ~ m1_subset_1(X230,k1_zfmisc_1(X231))
      | ~ v1_xboole_0(X231) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk45_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v3_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_tex_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X212,X213,X214] :
      ( ~ m1_subset_1(X214,k1_zfmisc_1(X212))
      | k9_subset_1(X212,X213,X214) = k3_xboole_0(X213,X214) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk45_2(esk1_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

fof(c_0_24,plain,(
    ! [X105,X106,X107] :
      ( ~ m1_subset_1(X107,k1_zfmisc_1(X105))
      | k9_subset_1(X105,X106,X107) = k9_subset_1(X105,X107,X106) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_25,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X210,X211] :
      ( v1_xboole_0(X210)
      | ~ m1_subset_1(X211,X210)
      | k6_domain_1(X210,X211) = k1_tarski(X211) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk45_2(X1,X2),u1_struct_0(X1))
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_29,plain,(
    ! [X110,X111] :
      ( v1_xboole_0(X110)
      | ~ m1_subset_1(X111,X110)
      | m1_subset_1(k6_domain_1(X110,X111),k1_zfmisc_1(X110)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_30,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) = k3_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_15])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk45_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_15])).

fof(c_0_35,plain,(
    ! [X103,X104] : k3_xboole_0(X103,X104) = k3_xboole_0(X104,X103) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X108,X109] :
      ( ~ l1_pre_topc(X108)
      | ~ m1_subset_1(X109,k1_zfmisc_1(u1_struct_0(X108)))
      | m1_subset_1(k2_pre_topc(X108,X109),k1_zfmisc_1(u1_struct_0(X108))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_38,plain,
    ( v2_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != k6_domain_1(u1_struct_0(X2),esk45_2(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v3_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k3_xboole_0(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_15]),c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk45_2(esk1_0,esk2_0)) = k1_tarski(esk45_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),X1))) = k6_domain_1(u1_struct_0(esk1_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X125,X126] :
      ( ~ v2_pre_topc(X125)
      | ~ l1_pre_topc(X125)
      | ~ m1_subset_1(X126,k1_zfmisc_1(u1_struct_0(X125)))
      | v4_pre_topc(k2_pre_topc(X125,X126),X125) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk45_2(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_34])).

cnf(c_0_45,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k3_xboole_0(X1,esk2_0) != k1_tarski(esk45_2(esk1_0,esk2_0))
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),X1))) = k6_domain_1(u1_struct_0(esk1_0),X1)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_39]),c_0_42])).

cnf(c_0_48,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk45_2(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk45_2(esk1_0,esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_44]),c_0_16])])).

cnf(c_0_51,negated_conjecture,
    ( k3_xboole_0(esk2_0,X1) != k1_tarski(esk45_2(esk1_0,esk2_0))
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_pre_topc(esk1_0,k1_tarski(esk45_2(esk1_0,esk2_0)))) = k1_tarski(esk45_2(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_23]),c_0_33])]),c_0_40]),c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,k1_tarski(esk45_2(esk1_0,esk2_0))),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_16]),c_0_18])])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,k1_tarski(esk45_2(esk1_0,esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_50,c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
