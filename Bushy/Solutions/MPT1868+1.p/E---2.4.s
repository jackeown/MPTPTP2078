%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t36_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:31 EDT 2019

% Result     : Theorem 0.81s
% Output     : CNFRefutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 424 expanded)
%              Number of clauses        :   55 ( 168 expanded)
%              Number of leaves         :   21 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          :  273 (1421 expanded)
%              Number of equality atoms :   48 ( 104 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',t36_tex_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',dt_l1_pre_topc)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',redefinition_k6_domain_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',dt_k6_domain_1)).

fof(d5_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r1_tarski(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',d5_tex_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',t6_boole)).

fof(fc3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => v1_xboole_0(k1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',fc3_struct_0)).

fof(t39_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',t39_zfmisc_1)).

fof(dt_k1_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',dt_k1_struct_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',t28_xboole_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',redefinition_k9_subset_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',dt_o_0_0_xboole_0)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',commutativity_k9_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',dt_k9_subset_1)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',dt_k2_struct_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',d3_struct_0)).

fof(cc1_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',cc1_tops_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',commutativity_k3_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',t3_subset)).

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',fc10_tops_1)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t36_tex_2])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ~ v2_tex_2(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_23,plain,(
    ! [X36] :
      ( v2_struct_0(X36)
      | ~ l1_struct_0(X36)
      | ~ v1_xboole_0(u1_struct_0(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_26,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_27,plain,(
    ! [X42,X43] :
      ( v1_xboole_0(X42)
      | ~ m1_subset_1(X43,X42)
      | k6_domain_1(X42,X43) = k1_tarski(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_28,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ m1_subset_1(X26,X25)
      | m1_subset_1(k6_domain_1(X25,X26),k1_zfmisc_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

fof(c_0_35,plain,(
    ! [X17,X18,X19,X22] :
      ( ( m1_subset_1(esk3_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r1_tarski(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( v3_pre_topc(esk3_3(X17,X18,X19),X17)
        | ~ r1_tarski(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( k9_subset_1(u1_struct_0(X17),X18,esk3_3(X17,X18,X19)) = X19
        | ~ r1_tarski(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk4_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))
        | v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( r1_tarski(esk4_2(X17,X18),X18)
        | v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_pre_topc(X22,X17)
        | k9_subset_1(u1_struct_0(X17),X18,X22) != esk4_2(X17,X18)
        | v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk2_0) = k1_tarski(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_39,plain,(
    ! [X64] :
      ( ~ v1_xboole_0(X64)
      | X64 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_40,plain,(
    ! [X37] :
      ( ~ l1_struct_0(X37)
      | v1_xboole_0(k1_struct_0(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_struct_0])])).

fof(c_0_41,plain,(
    ! [X54,X55] :
      ( ( ~ r1_tarski(X54,k1_tarski(X55))
        | X54 = k1_xboole_0
        | X54 = k1_tarski(X55) )
      & ( X54 != k1_xboole_0
        | r1_tarski(X54,k1_tarski(X55)) )
      & ( X54 != k1_tarski(X55)
        | r1_tarski(X54,k1_tarski(X55)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).

cnf(c_0_42,plain,
    ( r1_tarski(esk4_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_37]),c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_tex_2(k1_tarski(esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_37])).

fof(c_0_45,plain,(
    ! [X23] :
      ( ~ l1_struct_0(X23)
      | m1_subset_1(k1_struct_0(X23),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_struct_0])])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_48,plain,(
    ! [X49,X50] :
      ( ~ r1_tarski(X49,X50)
      | k3_xboole_0(X49,X50) = X49 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_49,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(X44))
      | k9_subset_1(X44,X45,X46) = k3_xboole_0(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk4_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_30])]),c_0_44])).

cnf(c_0_52,plain,
    ( m1_subset_1(k1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_55,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | k9_subset_1(X13,X14,X15) = k9_subset_1(X13,X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

fof(c_0_56,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X27))
      | m1_subset_1(k9_subset_1(X27,X28,X29),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk4_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_60,negated_conjecture,
    ( esk4_2(esk1_0,k1_tarski(esk2_0)) = k1_tarski(esk2_0)
    | esk4_2(esk1_0,k1_tarski(esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_61,plain,(
    ! [X24] :
      ( ~ l1_struct_0(X24)
      | m1_subset_1(k2_struct_0(X24),k1_zfmisc_1(u1_struct_0(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

fof(c_0_62,plain,(
    ! [X16] :
      ( ~ l1_struct_0(X16)
      | k2_struct_0(X16) = u1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_63,plain,(
    ! [X9,X10] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ v1_xboole_0(X10)
      | v3_pre_topc(X10,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).

cnf(c_0_64,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_65,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_54])).

cnf(c_0_66,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,plain,
    ( k9_subset_1(X1,X2,X3) = X2
    | ~ r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( esk4_2(esk1_0,k1_tarski(esk2_0)) = k1_xboole_0
    | k9_subset_1(u1_struct_0(esk1_0),k1_tarski(esk2_0),X1) != k1_tarski(esk2_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_43]),c_0_30])]),c_0_44])).

cnf(c_0_70,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_72,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_73,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_29])).

cnf(c_0_75,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_65])).

cnf(c_0_76,plain,
    ( v2_tex_2(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk4_2(X2,X1)
    | ~ v3_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_66])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( esk4_2(esk1_0,k1_tarski(esk2_0)) = k1_xboole_0
    | k3_xboole_0(k1_tarski(esk2_0),X1) != k1_tarski(esk2_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_58])).

cnf(c_0_79,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,plain,
    ( v3_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

cnf(c_0_82,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_83,plain,
    ( v2_tex_2(X1,X2)
    | ~ v3_pre_topc(esk4_2(X2,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_68])]),c_0_77]),c_0_42])).

cnf(c_0_84,negated_conjecture,
    ( esk4_2(esk1_0,k1_tarski(esk2_0)) = k1_xboole_0
    | k3_xboole_0(u1_struct_0(esk1_0),k1_tarski(esk2_0)) != k1_tarski(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v3_pre_topc(u1_struct_0(esk1_0),esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( v3_pre_topc(k1_xboole_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_30])])).

cnf(c_0_86,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk1_0),k1_tarski(esk2_0)) != k1_tarski(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ v3_pre_topc(u1_struct_0(esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_43]),c_0_30])]),c_0_44])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_80])).

fof(c_0_88,plain,(
    ! [X56,X57] :
      ( ( ~ m1_subset_1(X56,k1_zfmisc_1(X57))
        | r1_tarski(X56,X57) )
      & ( ~ r1_tarski(X56,X57)
        | m1_subset_1(X56,k1_zfmisc_1(X57)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_89,plain,(
    ! [X35] :
      ( ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | v3_pre_topc(k2_struct_0(X35),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(esk2_0),u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ v3_pre_topc(u1_struct_0(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_92,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ v3_pre_topc(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_43])])).

cnf(c_0_94,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_71]),c_0_29])).

cnf(c_0_95,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_30]),c_0_82])])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_29]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
