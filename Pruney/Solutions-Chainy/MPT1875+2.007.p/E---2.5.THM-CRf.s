%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:13 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 133 expanded)
%              Number of clauses        :   31 (  48 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  236 ( 609 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc5_tdlat_3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_borsuk_1(X2,X1)
            & v1_tsep_1(X2,X1)
            & v1_tdlat_3(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(t43_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(t26_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v2_tex_2(X3,X1)
                <=> v1_tdlat_3(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t37_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) )
           => v2_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_12,plain,(
    ! [X20,X21] :
      ( ( v1_borsuk_1(X21,X20)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ v1_tdlat_3(X20)
        | ~ l1_pre_topc(X20) )
      & ( v1_tsep_1(X21,X20)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ v1_tdlat_3(X20)
        | ~ l1_pre_topc(X20) )
      & ( v1_tdlat_3(X21)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ v1_tdlat_3(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_tdlat_3])])])])])).

fof(c_0_13,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | ~ v1_tdlat_3(X19)
      | v2_pre_topc(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v2_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t43_tex_2])).

cnf(c_0_15,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X9,X10] :
      ( ( v1_pre_topc(k1_pre_topc(X9,X10))
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9))) )
      & ( m1_pre_topc(k1_pre_topc(X9,X10),X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_18,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v2_tex_2(X24,X22)
        | v1_tdlat_3(X23)
        | X24 != u1_struct_0(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ v1_tdlat_3(X23)
        | v2_tex_2(X24,X22)
        | X24 != u1_struct_0(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

fof(c_0_19,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | m1_subset_1(u1_struct_0(X18),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | u1_struct_0(k1_pre_topc(X15,X16)) = X16 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v1_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_22,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X2)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v1_tdlat_3(k1_pre_topc(X1,X2))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v1_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_32,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_33,plain,(
    ! [X25,X26,X28] :
      ( ( m1_subset_1(esk2_2(X25,X26),u1_struct_0(X25))
        | v2_tex_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( r2_hidden(esk2_2(X25,X26),X26)
        | v2_tex_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ v3_pre_topc(X28,X25)
        | k9_subset_1(u1_struct_0(X25),X26,X28) != k6_domain_1(u1_struct_0(X25),esk2_2(X25,X26))
        | v2_tex_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_tex_2])])])])])])).

fof(c_0_34,plain,(
    ! [X14] :
      ( ~ v2_struct_0(X14)
      | ~ l1_struct_0(X14)
      | v1_xboole_0(u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

cnf(c_0_35,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk3_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_37,negated_conjecture,
    ( v1_tdlat_3(k1_pre_topc(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_30]),c_0_28])]),c_0_31])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X12,X13] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | l1_pre_topc(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_41,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( v2_tex_2(esk4_0,X1)
    | v2_struct_0(k1_pre_topc(esk3_0,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k1_pre_topc(esk3_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,plain,
    ( v2_tex_2(X1,X2)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v2_struct_0(k1_pre_topc(esk3_0,esk4_0))
    | ~ l1_struct_0(k1_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( v2_struct_0(k1_pre_topc(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_23]),c_0_28]),c_0_27])]),c_0_43]),c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_45]),c_0_28])]),c_0_43]),c_0_31])).

fof(c_0_50,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | l1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_51,plain,
    ( l1_pre_topc(k1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( ~ l1_struct_0(k1_pre_topc(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])]),c_0_49])).

cnf(c_0_53,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_27]),c_0_28])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.30  % Computer   : n025.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % WCLimit    : 600
% 0.09/0.30  % DateTime   : Tue Dec  1 10:47:50 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.30  # Version: 2.5pre002
% 0.09/0.30  # No SInE strategy applied
% 0.09/0.30  # Trying AutoSched0 for 299 seconds
% 0.15/0.32  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.15/0.32  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.15/0.32  #
% 0.15/0.32  # Preprocessing time       : 0.014 s
% 0.15/0.32  
% 0.15/0.32  # Proof found!
% 0.15/0.32  # SZS status Theorem
% 0.15/0.32  # SZS output start CNFRefutation
% 0.15/0.32  fof(cc5_tdlat_3, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_borsuk_1(X2,X1)&v1_tsep_1(X2,X1))&v1_tdlat_3(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 0.15/0.32  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.15/0.32  fof(t43_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 0.15/0.32  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.15/0.32  fof(t26_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v2_tex_2(X3,X1)<=>v1_tdlat_3(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 0.15/0.32  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.15/0.32  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.15/0.32  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.15/0.32  fof(t37_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k6_domain_1(u1_struct_0(X1),X3)))))))=>v2_tex_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_tex_2)).
% 0.15/0.32  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.15/0.32  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.15/0.32  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.15/0.32  fof(c_0_12, plain, ![X20, X21]:(((v1_borsuk_1(X21,X20)|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~v1_tdlat_3(X20)|~l1_pre_topc(X20)))&(v1_tsep_1(X21,X20)|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~v1_tdlat_3(X20)|~l1_pre_topc(X20))))&(v1_tdlat_3(X21)|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~v1_tdlat_3(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_tdlat_3])])])])])).
% 0.15/0.32  fof(c_0_13, plain, ![X19]:(~l1_pre_topc(X19)|(~v1_tdlat_3(X19)|v2_pre_topc(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.15/0.32  fof(c_0_14, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t43_tex_2])).
% 0.15/0.32  cnf(c_0_15, plain, (v1_tdlat_3(X1)|v2_struct_0(X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.32  cnf(c_0_16, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.32  fof(c_0_17, plain, ![X9, X10]:((v1_pre_topc(k1_pre_topc(X9,X10))|(~l1_pre_topc(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))))&(m1_pre_topc(k1_pre_topc(X9,X10),X9)|(~l1_pre_topc(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.15/0.32  fof(c_0_18, plain, ![X22, X23, X24]:((~v2_tex_2(X24,X22)|v1_tdlat_3(X23)|X24!=u1_struct_0(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~l1_pre_topc(X22)))&(~v1_tdlat_3(X23)|v2_tex_2(X24,X22)|X24!=u1_struct_0(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~l1_pre_topc(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).
% 0.15/0.32  fof(c_0_19, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|m1_subset_1(u1_struct_0(X18),k1_zfmisc_1(u1_struct_0(X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.15/0.32  fof(c_0_20, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|u1_struct_0(k1_pre_topc(X15,X16))=X16)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.15/0.32  fof(c_0_21, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v1_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&~v2_tex_2(esk4_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.15/0.32  cnf(c_0_22, plain, (v1_tdlat_3(X1)|v2_struct_0(X2)|~v1_tdlat_3(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_15, c_0_16])).
% 0.15/0.32  cnf(c_0_23, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.32  cnf(c_0_24, plain, (v2_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X3)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.32  cnf(c_0_25, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.32  cnf(c_0_26, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.32  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.32  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.32  cnf(c_0_29, plain, (v1_tdlat_3(k1_pre_topc(X1,X2))|v2_struct_0(X1)|~v1_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.15/0.32  cnf(c_0_30, negated_conjecture, (v1_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.32  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.32  fof(c_0_32, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.15/0.32  fof(c_0_33, plain, ![X25, X26, X28]:((m1_subset_1(esk2_2(X25,X26),u1_struct_0(X25))|v2_tex_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&((r2_hidden(esk2_2(X25,X26),X26)|v2_tex_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X25)))|(~v3_pre_topc(X28,X25)|k9_subset_1(u1_struct_0(X25),X26,X28)!=k6_domain_1(u1_struct_0(X25),esk2_2(X25,X26)))|v2_tex_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_tex_2])])])])])])).
% 0.15/0.32  fof(c_0_34, plain, ![X14]:(~v2_struct_0(X14)|~l1_struct_0(X14)|v1_xboole_0(u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.15/0.32  cnf(c_0_35, plain, (v2_tex_2(u1_struct_0(X1),X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]), c_0_25])).
% 0.15/0.32  cnf(c_0_36, negated_conjecture, (u1_struct_0(k1_pre_topc(esk3_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.15/0.32  cnf(c_0_37, negated_conjecture, (v1_tdlat_3(k1_pre_topc(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_27]), c_0_30]), c_0_28])]), c_0_31])).
% 0.15/0.32  cnf(c_0_38, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.15/0.32  cnf(c_0_39, plain, (r2_hidden(esk2_2(X1,X2),X2)|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.15/0.32  fof(c_0_40, plain, ![X12, X13]:(~l1_pre_topc(X12)|(~m1_pre_topc(X13,X12)|l1_pre_topc(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.15/0.32  cnf(c_0_41, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.15/0.32  cnf(c_0_42, negated_conjecture, (v2_tex_2(esk4_0,X1)|v2_struct_0(k1_pre_topc(esk3_0,esk4_0))|v2_struct_0(X1)|~m1_pre_topc(k1_pre_topc(esk3_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.15/0.32  cnf(c_0_43, negated_conjecture, (~v2_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.32  cnf(c_0_44, plain, (v2_tex_2(X1,X2)|v2_struct_0(X2)|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.15/0.32  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.32  cnf(c_0_46, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.32  cnf(c_0_47, negated_conjecture, (v1_xboole_0(esk4_0)|~v2_struct_0(k1_pre_topc(esk3_0,esk4_0))|~l1_struct_0(k1_pre_topc(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_36])).
% 0.15/0.32  cnf(c_0_48, negated_conjecture, (v2_struct_0(k1_pre_topc(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_23]), c_0_28]), c_0_27])]), c_0_43]), c_0_31])).
% 0.15/0.32  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_45]), c_0_28])]), c_0_43]), c_0_31])).
% 0.15/0.32  fof(c_0_50, plain, ![X11]:(~l1_pre_topc(X11)|l1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.15/0.32  cnf(c_0_51, plain, (l1_pre_topc(k1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_23])).
% 0.15/0.32  cnf(c_0_52, negated_conjecture, (~l1_struct_0(k1_pre_topc(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])]), c_0_49])).
% 0.15/0.32  cnf(c_0_53, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.15/0.32  cnf(c_0_54, negated_conjecture, (l1_pre_topc(k1_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_27]), c_0_28])])).
% 0.15/0.32  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])]), ['proof']).
% 0.15/0.32  # SZS output end CNFRefutation
% 0.15/0.32  # Proof object total steps             : 56
% 0.15/0.32  # Proof object clause steps            : 31
% 0.15/0.32  # Proof object formula steps           : 25
% 0.15/0.32  # Proof object conjectures             : 18
% 0.15/0.32  # Proof object clause conjectures      : 15
% 0.15/0.32  # Proof object formula conjectures     : 3
% 0.15/0.32  # Proof object initial clauses used    : 17
% 0.15/0.32  # Proof object initial formulas used   : 12
% 0.15/0.32  # Proof object generating inferences   : 11
% 0.15/0.32  # Proof object simplifying inferences  : 28
% 0.15/0.32  # Training examples: 0 positive, 0 negative
% 0.15/0.32  # Parsed axioms                        : 12
% 0.15/0.32  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.32  # Initial clauses                      : 24
% 0.15/0.32  # Removed in clause preprocessing      : 0
% 0.15/0.32  # Initial clauses in saturation        : 24
% 0.15/0.32  # Processed clauses                    : 61
% 0.15/0.32  # ...of these trivial                  : 0
% 0.15/0.32  # ...subsumed                          : 5
% 0.15/0.32  # ...remaining for further processing  : 56
% 0.15/0.32  # Other redundant clauses eliminated   : 2
% 0.15/0.32  # Clauses deleted for lack of memory   : 0
% 0.15/0.32  # Backward-subsumed                    : 1
% 0.15/0.32  # Backward-rewritten                   : 5
% 0.15/0.32  # Generated clauses                    : 85
% 0.15/0.32  # ...of the previous two non-trivial   : 76
% 0.15/0.32  # Contextual simplify-reflections      : 6
% 0.15/0.32  # Paramodulations                      : 83
% 0.15/0.32  # Factorizations                       : 0
% 0.15/0.32  # Equation resolutions                 : 2
% 0.15/0.32  # Propositional unsat checks           : 0
% 0.15/0.32  #    Propositional check models        : 0
% 0.15/0.32  #    Propositional check unsatisfiable : 0
% 0.15/0.32  #    Propositional clauses             : 0
% 0.15/0.32  #    Propositional clauses after purity: 0
% 0.15/0.32  #    Propositional unsat core size     : 0
% 0.15/0.32  #    Propositional preprocessing time  : 0.000
% 0.15/0.32  #    Propositional encoding time       : 0.000
% 0.15/0.32  #    Propositional solver time         : 0.000
% 0.15/0.32  #    Success case prop preproc time    : 0.000
% 0.15/0.32  #    Success case prop encoding time   : 0.000
% 0.15/0.32  #    Success case prop solver time     : 0.000
% 0.15/0.32  # Current number of processed clauses  : 48
% 0.15/0.32  #    Positive orientable unit clauses  : 9
% 0.15/0.32  #    Positive unorientable unit clauses: 0
% 0.15/0.32  #    Negative unit clauses             : 4
% 0.15/0.32  #    Non-unit-clauses                  : 35
% 0.15/0.32  # Current number of unprocessed clauses: 39
% 0.15/0.32  # ...number of literals in the above   : 241
% 0.15/0.32  # Current number of archived formulas  : 0
% 0.15/0.32  # Current number of archived clauses   : 6
% 0.15/0.32  # Clause-clause subsumption calls (NU) : 590
% 0.15/0.32  # Rec. Clause-clause subsumption calls : 55
% 0.15/0.32  # Non-unit clause-clause subsumptions  : 9
% 0.15/0.32  # Unit Clause-clause subsumption calls : 39
% 0.15/0.32  # Rewrite failures with RHS unbound    : 0
% 0.15/0.32  # BW rewrite match attempts            : 1
% 0.15/0.32  # BW rewrite match successes           : 1
% 0.15/0.32  # Condensation attempts                : 0
% 0.15/0.32  # Condensation successes               : 0
% 0.15/0.32  # Termbank termtop insertions          : 4232
% 0.15/0.32  
% 0.15/0.32  # -------------------------------------------------
% 0.15/0.32  # User time                : 0.015 s
% 0.15/0.32  # System time              : 0.003 s
% 0.15/0.32  # Total time               : 0.018 s
% 0.15/0.32  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
