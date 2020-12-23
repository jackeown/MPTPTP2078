%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t44_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:50 EDT 2019

% Result     : Theorem 72.44s
% Output     : CNFRefutation 72.44s
% Verified   : 
% Statistics : Number of formulae       :  171 (6233 expanded)
%              Number of clauses        :  117 (2587 expanded)
%              Number of leaves         :   27 (1602 expanded)
%              Depth                    :   23
%              Number of atoms          :  483 (23483 expanded)
%              Number of equality atoms :   64 (1111 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_tex_2(X2,X1)
          <=> v1_zfmisc_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',t44_tex_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',t4_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',fc2_struct_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',d1_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',dt_l1_pre_topc)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',redefinition_k6_domain_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',dt_k6_domain_1)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',d1_tex_2)).

fof(fc2_zfmisc_1,axiom,(
    ! [X1] : v1_zfmisc_1(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',fc2_zfmisc_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',fc2_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',t1_subset)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',t28_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',t3_subset)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',dt_k9_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',redefinition_k9_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',t5_subset)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',t2_boole)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',existence_m1_subset_1)).

fof(redefinition_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ! [X3] :
          ( m2_subset_1(X3,X1,X2)
        <=> m1_subset_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',redefinition_m2_subset_1)).

fof(t32_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k1_tarski(X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',t32_tex_2)).

fof(t20_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v2_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ~ ( v3_pre_topc(X2,X1)
                & X2 != k1_xboole_0
                & X2 != u1_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',t20_tdlat_3)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',idempotence_k9_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',fc1_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',commutativity_k3_xboole_0)).

fof(dt_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ! [X3] :
          ( m2_subset_1(X3,X1,X2)
         => m1_subset_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',dt_m2_subset_1)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t44_tex_2.p',t36_tex_2)).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v2_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v2_tex_2(X2,X1)
            <=> v1_zfmisc_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_tex_2])).

fof(c_0_28,plain,(
    ! [X72,X73,X74] :
      ( ~ r2_hidden(X72,X73)
      | ~ m1_subset_1(X73,k1_zfmisc_1(X74))
      | m1_subset_1(X72,X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & v2_tdlat_3(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v2_tex_2(esk2_0,esk1_0)
      | ~ v1_zfmisc_1(esk2_0) )
    & ( v2_tex_2(esk2_0,esk1_0)
      | v1_zfmisc_1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).

fof(c_0_30,plain,(
    ! [X37] :
      ( v2_struct_0(X37)
      | ~ l1_struct_0(X37)
      | ~ v1_xboole_0(u1_struct_0(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v1_xboole_0(X17)
        | ~ r2_hidden(X18,X17) )
      & ( r2_hidden(esk4_1(X19),X19)
        | v1_xboole_0(X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X26] :
      ( ~ l1_pre_topc(X26)
      | l1_struct_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_37,plain,(
    ! [X46,X47] :
      ( v1_xboole_0(X46)
      | ~ m1_subset_1(X47,X46)
      | k6_domain_1(X46,X47) = k1_tarski(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_44,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X21)
      | ~ m1_subset_1(X22,X21)
      | m1_subset_1(k6_domain_1(X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk4_1(esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

fof(c_0_48,plain,(
    ! [X14,X16] :
      ( ( m1_subset_1(esk3_1(X14),X14)
        | ~ v1_zfmisc_1(X14)
        | v1_xboole_0(X14) )
      & ( X14 = k6_domain_1(X14,esk3_1(X14))
        | ~ v1_zfmisc_1(X14)
        | v1_xboole_0(X14) )
      & ( ~ m1_subset_1(X16,X14)
        | X14 != k6_domain_1(X14,X16)
        | v1_zfmisc_1(X14)
        | v1_xboole_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

fof(c_0_49,plain,(
    ! [X39] : v1_zfmisc_1(k1_tarski(X39)) ),
    inference(variable_rename,[status(thm)],[fc2_zfmisc_1])).

fof(c_0_50,plain,(
    ! [X38] : ~ v1_xboole_0(k1_tarski(X38)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk4_1(esk2_0)) = k1_tarski(esk4_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

fof(c_0_53,plain,(
    ! [X62,X63] :
      ( ~ m1_subset_1(X62,X63)
      | v1_xboole_0(X63)
      | r2_hidden(X62,X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_54,plain,
    ( m1_subset_1(esk3_1(X1),X1)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( v1_zfmisc_1(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_57,plain,(
    ! [X54,X55] :
      ( ~ r2_hidden(X54,X55)
      | m1_subset_1(X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk4_1(esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_46]),c_0_47]),c_0_52])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk3_1(k1_tarski(X1)),k1_tarski(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( X1 = k6_domain_1(X1,esk3_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,k1_tarski(esk4_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_58])).

cnf(c_0_64,plain,
    ( r2_hidden(esk3_1(k1_tarski(X1)),k1_tarski(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_56])).

cnf(c_0_65,plain,
    ( m1_subset_1(esk4_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_39])).

fof(c_0_66,plain,(
    ! [X59,X60] :
      ( ~ r1_tarski(X59,X60)
      | k3_xboole_0(X59,X60) = X59 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_67,plain,(
    ! [X70,X71] :
      ( ( ~ m1_subset_1(X70,k1_zfmisc_1(X71))
        | r1_tarski(X70,X71) )
      & ( ~ r1_tarski(X70,X71)
        | m1_subset_1(X70,k1_zfmisc_1(X71)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_68,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X23))
      | m1_subset_1(k9_subset_1(X23,X24,X25),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_69,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(X48))
      | k9_subset_1(X48,X49,X50) = k3_xboole_0(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_70,plain,
    ( k6_domain_1(k1_tarski(X1),esk3_1(k1_tarski(X1))) = k1_tarski(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_55]),c_0_56])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk3_1(k1_tarski(esk4_1(esk2_0))),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( k6_domain_1(X1,esk4_1(X1)) = k1_tarski(esk4_1(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_65])).

fof(c_0_73,plain,(
    ! [X75,X76,X77] :
      ( ~ r2_hidden(X75,X76)
      | ~ m1_subset_1(X76,k1_zfmisc_1(X77))
      | ~ v1_xboole_0(X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_74,plain,(
    ! [X61] : k3_xboole_0(X61,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( k1_tarski(esk3_1(k1_tarski(X1))) = k1_tarski(X1) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_60]),c_0_56]),c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk3_1(k6_domain_1(esk2_0,esk4_1(esk2_0))),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_40])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

fof(c_0_84,plain,(
    ! [X32] : m1_subset_1(esk7_1(X32),X32) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_85,plain,(
    ! [X51,X52,X53] :
      ( ( ~ m2_subset_1(X53,X51,X52)
        | m1_subset_1(X53,X52)
        | v1_xboole_0(X51)
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X51)) )
      & ( ~ m1_subset_1(X53,X52)
        | m2_subset_1(X53,X51,X52)
        | v1_xboole_0(X51)
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_m2_subset_1])])])])])).

cnf(c_0_86,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk3_1(k1_tarski(esk4_1(esk2_0)))) = k1_tarski(esk4_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_71]),c_0_47]),c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk3_1(k6_domain_1(esk2_0,esk4_1(esk2_0)))) = k1_tarski(esk3_1(k6_domain_1(esk2_0,esk4_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_80]),c_0_47])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,k9_subset_1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_77])).

cnf(c_0_90,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

fof(c_0_92,plain,(
    ! [X64,X65,X66] :
      ( ( m1_subset_1(esk11_3(X64,X65,X66),k1_zfmisc_1(u1_struct_0(X64)))
        | ~ r2_hidden(X66,X65)
        | ~ m1_subset_1(X66,u1_struct_0(X64))
        | ~ v2_tex_2(X65,X64)
        | ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))
        | ~ l1_pre_topc(X64) )
      & ( v3_pre_topc(esk11_3(X64,X65,X66),X64)
        | ~ r2_hidden(X66,X65)
        | ~ m1_subset_1(X66,u1_struct_0(X64))
        | ~ v2_tex_2(X65,X64)
        | ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))
        | ~ l1_pre_topc(X64) )
      & ( k9_subset_1(u1_struct_0(X64),X65,esk11_3(X64,X65,X66)) = k1_tarski(X66)
        | ~ r2_hidden(X66,X65)
        | ~ m1_subset_1(X66,u1_struct_0(X64))
        | ~ v2_tex_2(X65,X64)
        | ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))
        | ~ l1_pre_topc(X64) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_tex_2])])])])])).

cnf(c_0_93,plain,
    ( m2_subset_1(X1,X3,X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_94,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_83])).

cnf(c_0_95,plain,
    ( m1_subset_1(k6_domain_1(X1,esk4_1(X1)),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_65])).

cnf(c_0_96,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_60]),c_0_56]),c_0_70])).

cnf(c_0_97,negated_conjecture,
    ( k1_tarski(esk3_1(k6_domain_1(esk2_0,esk4_1(esk2_0)))) = k6_domain_1(esk2_0,esk4_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_72]),c_0_40]),c_0_88])).

cnf(c_0_98,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ v1_xboole_0(X4) ),
    inference(spm,[status(thm)],[c_0_89,c_0_78])).

cnf(c_0_99,plain,
    ( esk7_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

fof(c_0_100,plain,(
    ! [X56,X57] :
      ( ( ~ v2_tdlat_3(X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ v3_pre_topc(X57,X56)
        | X57 = k1_xboole_0
        | X57 = u1_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( m1_subset_1(esk10_1(X56),k1_zfmisc_1(u1_struct_0(X56)))
        | v2_tdlat_3(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( v3_pre_topc(esk10_1(X56),X56)
        | v2_tdlat_3(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( esk10_1(X56) != k1_xboole_0
        | v2_tdlat_3(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( esk10_1(X56) != u1_struct_0(X56)
        | v2_tdlat_3(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_tdlat_3])])])])])).

cnf(c_0_101,plain,
    ( m1_subset_1(esk11_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_102,plain,
    ( v3_pre_topc(esk11_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_103,plain,
    ( m2_subset_1(X1,X2,k9_subset_1(X2,X3,X4))
    | v1_xboole_0(k9_subset_1(X2,X3,X4))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k9_subset_1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_77])).

cnf(c_0_104,plain,
    ( v1_xboole_0(k9_subset_1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_39])).

fof(c_0_105,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X41))
      | k9_subset_1(X41,X42,X42) = X42 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

cnf(c_0_106,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k6_domain_1(X2,esk4_1(X2)))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk2_0,esk4_1(esk2_0)),k1_zfmisc_1(k6_domain_1(esk2_0,esk4_1(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_108,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X4) ),
    inference(spm,[status(thm)],[c_0_98,c_0_83])).

cnf(c_0_109,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_99])).

cnf(c_0_110,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_111,plain,
    ( X2 = k1_xboole_0
    | X2 = u1_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_112,plain,
    ( m1_subset_1(esk11_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_101,c_0_31])).

cnf(c_0_113,plain,
    ( v3_pre_topc(esk11_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_102,c_0_31])).

cnf(c_0_114,plain,
    ( m2_subset_1(esk4_1(k9_subset_1(X1,X2,X3)),X1,k9_subset_1(X1,X2,X3))
    | v1_xboole_0(k9_subset_1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_65]),c_0_104])).

cnf(c_0_115,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk2_0,esk4_1(esk2_0)),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_40])).

cnf(c_0_117,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110])])).

cnf(c_0_118,plain,
    ( r2_hidden(esk7_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_91])).

cnf(c_0_119,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk11_3(X1,X2,X3)) = k1_tarski(X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_120,plain,
    ( esk11_3(X1,X2,X3) = u1_struct_0(X1)
    | esk11_3(X1,X2,X3) = k1_xboole_0
    | ~ r2_hidden(X3,X2)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113])).

cnf(c_0_121,negated_conjecture,
    ( v2_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_122,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_123,plain,
    ( m1_subset_1(X1,X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m2_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_124,negated_conjecture,
    ( m2_subset_1(esk4_1(k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)),u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0))
    | v1_xboole_0(k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_32])).

cnf(c_0_125,plain,
    ( k9_subset_1(X1,X2,X2) = X2 ),
    inference(spm,[status(thm)],[c_0_115,c_0_91])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,k6_domain_1(esk2_0,esk4_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_116])).

cnf(c_0_127,plain,
    ( r2_hidden(esk3_1(k6_domain_1(X1,esk4_1(X1))),k6_domain_1(X1,esk4_1(X1)))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_72])).

fof(c_0_128,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_129,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_130,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk11_3(X1,X2,X3)) = k1_tarski(X3)
    | ~ r2_hidden(X3,X2)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_119,c_0_31])).

cnf(c_0_131,negated_conjecture,
    ( esk11_3(esk1_0,esk2_0,X1) = u1_struct_0(esk1_0)
    | esk11_3(esk1_0,esk2_0,X1) = k1_xboole_0
    | ~ r2_hidden(X1,esk2_0)
    | ~ v2_tex_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_32]),c_0_43]),c_0_121]),c_0_122])])).

cnf(c_0_132,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | v1_zfmisc_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_133,negated_conjecture,
    ( m1_subset_1(X1,esk2_0)
    | ~ m2_subset_1(X1,u1_struct_0(esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_32]),c_0_40]),c_0_47])).

cnf(c_0_134,negated_conjecture,
    ( m2_subset_1(esk4_1(esk2_0),u1_struct_0(esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_40])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(esk3_1(k6_domain_1(esk2_0,esk4_1(esk2_0))),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_40])).

cnf(c_0_136,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_128])).

fof(c_0_137,plain,(
    ! [X27,X28,X29] :
      ( v1_xboole_0(X27)
      | v1_xboole_0(X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | ~ m2_subset_1(X29,X27,X28)
      | m1_subset_1(X29,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_subset_1])])])])).

cnf(c_0_138,plain,
    ( v1_xboole_0(k9_subset_1(k1_xboole_0,X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_77])).

cnf(c_0_139,plain,
    ( k3_xboole_0(X1,esk11_3(X2,X1,X3)) = k1_tarski(X3)
    | ~ r2_hidden(X3,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_130]),c_0_112])).

cnf(c_0_140,negated_conjecture,
    ( esk11_3(esk1_0,esk2_0,X1) = u1_struct_0(esk1_0)
    | esk11_3(esk1_0,esk2_0,X1) = k1_xboole_0
    | v1_zfmisc_1(esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_141,negated_conjecture,
    ( m1_subset_1(esk4_1(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_142,plain,
    ( v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X2 != k6_domain_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_143,negated_conjecture,
    ( k6_domain_1(esk2_0,esk3_1(k6_domain_1(esk2_0,esk4_1(esk2_0)))) = k6_domain_1(esk2_0,esk4_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_135]),c_0_97]),c_0_40])).

cnf(c_0_144,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_136])).

cnf(c_0_145,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m2_subset_1(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_146,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_78])).

cnf(c_0_147,plain,
    ( k1_tarski(X1) = X2
    | ~ r2_hidden(X1,X2)
    | ~ v2_tex_2(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk11_3(X3,X2,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_83,c_0_139])).

cnf(c_0_148,negated_conjecture,
    ( esk11_3(esk1_0,esk2_0,esk4_1(esk2_0)) = u1_struct_0(esk1_0)
    | esk11_3(esk1_0,esk2_0,esk4_1(esk2_0)) = k1_xboole_0
    | v1_zfmisc_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_39]),c_0_40])).

cnf(c_0_149,negated_conjecture,
    ( k1_tarski(esk4_1(esk2_0)) = k6_domain_1(esk2_0,esk4_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_141]),c_0_40])).

cnf(c_0_150,negated_conjecture,
    ( r2_hidden(esk4_1(esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_141]),c_0_40])).

cnf(c_0_151,negated_conjecture,
    ( v1_zfmisc_1(esk2_0)
    | k6_domain_1(esk2_0,esk4_1(esk2_0)) != esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_135])]),c_0_40])).

cnf(c_0_152,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_144])).

fof(c_0_153,plain,(
    ! [X68,X69] :
      ( v2_struct_0(X68)
      | ~ v2_pre_topc(X68)
      | ~ l1_pre_topc(X68)
      | ~ m1_subset_1(X69,u1_struct_0(X68))
      | v2_tex_2(k6_domain_1(u1_struct_0(X68),X69),X68) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_154,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m2_subset_1(X1,u1_struct_0(esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_32]),c_0_40]),c_0_47])).

cnf(c_0_155,negated_conjecture,
    ( m2_subset_1(X1,u1_struct_0(esk1_0),esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_32]),c_0_40]),c_0_47])).

cnf(c_0_156,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v2_tex_2(X2,X3)
    | ~ m1_subset_1(esk11_3(X3,X2,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_139]),c_0_56])).

cnf(c_0_157,negated_conjecture,
    ( esk11_3(esk1_0,esk2_0,esk4_1(esk2_0)) = k1_xboole_0
    | v1_zfmisc_1(esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_148]),c_0_149]),c_0_150]),c_0_32]),c_0_43])]),c_0_132]),c_0_151])).

cnf(c_0_158,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_152,c_0_91])).

cnf(c_0_159,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_153])).

cnf(c_0_160,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_161,negated_conjecture,
    ( v1_zfmisc_1(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_157]),c_0_150]),c_0_158]),c_0_32]),c_0_43])]),c_0_132])).

cnf(c_0_162,negated_conjecture,
    ( v2_tex_2(k6_domain_1(u1_struct_0(esk1_0),X1),esk1_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_160]),c_0_43]),c_0_122])]),c_0_34])).

cnf(c_0_163,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),X1) = k1_tarski(X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_160]),c_0_47])).

cnf(c_0_164,negated_conjecture,
    ( m1_subset_1(esk3_1(esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_161]),c_0_40])).

cnf(c_0_165,negated_conjecture,
    ( k6_domain_1(esk2_0,esk3_1(esk2_0)) = esk2_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_161]),c_0_40])).

cnf(c_0_166,negated_conjecture,
    ( ~ v2_tex_2(esk2_0,esk1_0)
    | ~ v1_zfmisc_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_167,negated_conjecture,
    ( v2_tex_2(k1_tarski(X1),esk1_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_162,c_0_163])).

cnf(c_0_168,negated_conjecture,
    ( k1_tarski(esk3_1(esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_164]),c_0_40]),c_0_165])).

cnf(c_0_169,negated_conjecture,
    ( ~ v2_tex_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_166,c_0_161])])).

cnf(c_0_170,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_168]),c_0_164])]),c_0_169]),
    [proof]).
%------------------------------------------------------------------------------
