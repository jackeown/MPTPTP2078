%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t55_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:53 EDT 2019

% Result     : Theorem 151.97s
% Output     : CNFRefutation 151.97s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 880 expanded)
%              Number of clauses        :   96 ( 374 expanded)
%              Number of leaves         :   24 ( 214 expanded)
%              Depth                    :   18
%              Number of atoms          :  340 (3321 expanded)
%              Number of equality atoms :   42 ( 337 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
               => k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',t55_tex_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',dt_l1_pre_topc)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',fc2_struct_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',t2_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',d10_xboole_0)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',t37_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',t3_subset)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',fc1_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',dt_k2_pre_topc)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',redefinition_k9_subset_1)).

fof(t31_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v4_pre_topc(X2,X1)
                  & r1_tarski(X3,X2) )
               => r1_tarski(k2_pre_topc(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',t31_tops_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',redefinition_k6_domain_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',dt_k9_subset_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',t48_pre_topc)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',existence_m1_subset_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',d7_xboole_0)).

fof(t56_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',t56_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',t28_xboole_1)).

fof(t24_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',t24_tdlat_3)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',fc2_xboole_0)).

fof(t40_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r1_xboole_0(X2,X3)
                  & v3_pre_topc(X2,X1) )
               => r1_xboole_0(X2,k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',t40_tsep_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',commutativity_k3_xboole_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',t5_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t55_tex_2.p',fc1_xboole_0)).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
                 => k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t55_tex_2])).

fof(c_0_25,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | l1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & v3_tdlat_3(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & r2_hidden(esk2_0,k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk3_0)))
    & k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) != k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

fof(c_0_27,plain,(
    ! [X32] :
      ( v2_struct_0(X32)
      | ~ l1_struct_0(X32)
      | ~ v1_xboole_0(u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X55,X56] :
      ( ~ m1_subset_1(X55,X56)
      | v1_xboole_0(X56)
      | r2_hidden(X55,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_35,plain,(
    ! [X60,X61] :
      ( ( ~ r1_tarski(k1_tarski(X60),X61)
        | r2_hidden(X60,X61) )
      & ( ~ r2_hidden(X60,X61)
        | r1_tarski(k1_tarski(X60),X61) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

fof(c_0_39,plain,(
    ! [X62,X63] :
      ( ( ~ m1_subset_1(X62,k1_zfmisc_1(X63))
        | r1_tarski(X62,X63) )
      & ( ~ r1_tarski(X62,X63)
        | m1_subset_1(X62,k1_zfmisc_1(X63)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_41,plain,(
    ! [X30,X31] :
      ( ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | v4_pre_topc(k2_pre_topc(X30,X31),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

fof(c_0_44,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | m1_subset_1(k2_pre_topc(X18,X19),k1_zfmisc_1(u1_struct_0(X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_45,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X42))
      | k9_subset_1(X42,X43,X44) = k3_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_49,plain,(
    ! [X57,X58,X59] :
      ( ~ l1_pre_topc(X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
      | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X57)))
      | ~ v4_pre_topc(X58,X57)
      | ~ r1_tarski(X59,X58)
      | r1_tarski(k2_pre_topc(X57,X59),X58) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).

cnf(c_0_50,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_54,plain,(
    ! [X40,X41] :
      ( v1_xboole_0(X40)
      | ~ m1_subset_1(X41,X40)
      | k6_domain_1(X40,X41) = k1_tarski(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_55,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | m1_subset_1(k9_subset_1(X22,X23,X24),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_56,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_48]),c_0_38])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_pre_topc(X1,X3),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_29]),c_0_51])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk2_0,k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( k9_subset_1(X1,X2,X1) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_67,plain,(
    ! [X68,X69] :
      ( ~ l1_pre_topc(X68)
      | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
      | r1_tarski(X69,k2_pre_topc(X68,X69)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,X1),X2)
    | ~ v4_pre_topc(X2,esk1_0)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_29])).

cnf(c_0_70,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,k1_tarski(esk3_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,k1_tarski(esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk3_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk3_0) = k1_tarski(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_37]),c_0_38])).

cnf(c_0_74,negated_conjecture,
    ( k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) != k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_75,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_57])])).

cnf(c_0_76,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_77,plain,(
    ! [X28] : m1_subset_1(esk6_1(X28),X28) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,k1_tarski(esk3_0)))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,k1_tarski(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k2_pre_topc(esk1_0,k1_tarski(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( k2_pre_topc(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) != k2_pre_topc(esk1_0,k1_tarski(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk2_0) = k1_tarski(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_48]),c_0_38])).

fof(c_0_83,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k3_xboole_0(X16,X17) = k1_xboole_0 )
      & ( k3_xboole_0(X16,X17) != k1_xboole_0
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_84,plain,(
    ! [X73,X74] :
      ( r2_hidden(X73,X74)
      | r1_xboole_0(k1_tarski(X73),X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_zfmisc_1])])])).

cnf(c_0_85,plain,
    ( k9_subset_1(X1,X2,k3_xboole_0(X3,X1)) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_75])).

fof(c_0_86,plain,(
    ! [X52,X53] :
      ( ~ r1_tarski(X52,X53)
      | k3_xboole_0(X52,X53) = X52 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_29])).

cnf(c_0_88,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_89,plain,(
    ! [X49,X50] :
      ( ( ~ v3_tdlat_3(X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ v4_pre_topc(X50,X49)
        | v3_pre_topc(X50,X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( m1_subset_1(esk7_1(X49),k1_zfmisc_1(u1_struct_0(X49)))
        | v3_tdlat_3(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( v4_pre_topc(esk7_1(X49),X49)
        | v3_tdlat_3(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( ~ v3_pre_topc(esk7_1(X49),X49)
        | v3_tdlat_3(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

cnf(c_0_90,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,k1_tarski(esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_78])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,k1_tarski(esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_78])).

cnf(c_0_92,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,k1_tarski(esk2_0)),k2_pre_topc(esk1_0,k1_tarski(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_78]),c_0_80])])).

cnf(c_0_94,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tarski(esk3_0)) != k2_pre_topc(esk1_0,k1_tarski(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_95,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_98,plain,
    ( m1_subset_1(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k1_zfmisc_1(X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_75]),c_0_85])).

cnf(c_0_99,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k2_pre_topc(esk1_0,k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_78])).

fof(c_0_101,plain,(
    ! [X33] : ~ v1_xboole_0(k1_tarski(X33)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_102,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk6_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_88])).

fof(c_0_103,plain,(
    ! [X65,X66,X67] :
      ( ~ v2_pre_topc(X65)
      | ~ l1_pre_topc(X65)
      | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))
      | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X65)))
      | ~ r1_xboole_0(X66,X67)
      | ~ v3_pre_topc(X66,X65)
      | r1_xboole_0(X66,k2_pre_topc(X65,X67)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_tsep_1])])])).

cnf(c_0_104,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_105,negated_conjecture,
    ( v3_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_106,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,X1),k2_pre_topc(esk1_0,k1_tarski(esk2_0)))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,k1_tarski(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_90]),c_0_91])])).

cnf(c_0_108,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(esk1_0,k1_tarski(esk3_0)),k2_pre_topc(esk1_0,k1_tarski(esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_109,plain,
    ( k3_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_110,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_111,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk2_0),k2_pre_topc(esk1_0,k1_tarski(esk2_0))) = k1_tarski(esk2_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_112,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_113,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(k1_tarski(esk6_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_102])).

cnf(c_0_114,plain,
    ( r1_xboole_0(X2,k2_pre_topc(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X2,X3)
    | ~ v3_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_115,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_29]),c_0_105]),c_0_51])])).

cnf(c_0_116,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_117,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_118,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(esk3_0),k2_pre_topc(esk1_0,k1_tarski(esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_61]),c_0_108])).

cnf(c_0_119,plain,
    ( k3_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | r1_tarski(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_109])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,k1_tarski(esk2_0)),k2_pre_topc(esk1_0,k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_121,plain,
    ( r1_tarski(k1_tarski(esk6_1(k1_tarski(X1))),k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_122,negated_conjecture,
    ( r1_xboole_0(X1,k2_pre_topc(esk1_0,X2))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_29]),c_0_51])])).

cnf(c_0_123,negated_conjecture,
    ( v3_pre_topc(k2_pre_topc(esk1_0,k1_tarski(esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_90]),c_0_91])])).

cnf(c_0_124,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_125,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk3_0),k2_pre_topc(esk1_0,k1_tarski(esk2_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

fof(c_0_126,plain,(
    ! [X75,X76,X77] :
      ( ~ r2_hidden(X75,X76)
      | ~ m1_subset_1(X76,k1_zfmisc_1(X77))
      | ~ v1_xboole_0(X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(k3_xboole_0(k1_tarski(esk2_0),X1),k2_pre_topc(esk1_0,k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_120,c_0_117])).

cnf(c_0_128,plain,
    ( k3_xboole_0(k1_tarski(X1),k1_tarski(esk6_1(k1_tarski(X1)))) = k1_tarski(esk6_1(k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_121]),c_0_117])).

cnf(c_0_129,negated_conjecture,
    ( k3_xboole_0(k2_pre_topc(esk1_0,k1_tarski(esk2_0)),k2_pre_topc(esk1_0,k1_tarski(esk3_0))) = k2_pre_topc(esk1_0,k1_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_93])).

cnf(c_0_130,negated_conjecture,
    ( r1_xboole_0(k2_pre_topc(esk1_0,k1_tarski(esk2_0)),k2_pre_topc(esk1_0,X1))
    | ~ r1_xboole_0(k2_pre_topc(esk1_0,k1_tarski(esk2_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_91])])).

cnf(c_0_131,negated_conjecture,
    ( r1_xboole_0(k2_pre_topc(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_132,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_133,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_134,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(k1_tarski(esk6_1(k1_tarski(esk2_0))),k2_pre_topc(esk1_0,k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_136,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tarski(esk2_0)) = k1_xboole_0
    | ~ r1_xboole_0(k2_pre_topc(esk1_0,k1_tarski(esk2_0)),k2_pre_topc(esk1_0,k1_tarski(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_129])).

cnf(c_0_137,negated_conjecture,
    ( r1_xboole_0(k2_pre_topc(esk1_0,k1_tarski(esk2_0)),k2_pre_topc(esk1_0,k1_tarski(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_61]),c_0_131])])).

cnf(c_0_138,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_139,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_134,c_0_47])).

cnf(c_0_140,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk6_1(k1_tarski(esk2_0))),k1_zfmisc_1(k2_pre_topc(esk1_0,k1_tarski(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_135])).

cnf(c_0_141,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tarski(esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_136,c_0_137])])).

cnf(c_0_142,plain,
    ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_143,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_141]),c_0_142]),
    [proof]).
%------------------------------------------------------------------------------
