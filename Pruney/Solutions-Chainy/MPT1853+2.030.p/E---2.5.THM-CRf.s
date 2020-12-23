%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:29 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 304 expanded)
%              Number of clauses        :   47 ( 115 expanded)
%              Number of leaves         :   16 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  296 (1352 expanded)
%              Number of equality atoms :   18 (  38 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v1_tex_2(k1_tex_2(X1,X2),X1)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(t7_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => v1_subset_1(k6_domain_1(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(cc1_zfmisc_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_zfmisc_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(d3_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(cc1_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( v1_subset_1(X2,X1)
           => v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t6_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(t15_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ~ ( u1_struct_0(X2) = u1_struct_0(X1)
              & v1_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_17,plain,(
    ! [X34,X35] :
      ( v1_xboole_0(X34)
      | v1_zfmisc_1(X34)
      | ~ m1_subset_1(X35,X34)
      | v1_subset_1(k6_domain_1(X34,X35),X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).

fof(c_0_18,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | v1_zfmisc_1(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ( ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) )
    & ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v1_tex_2(X21,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | X22 != u1_struct_0(X21)
        | v1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk2_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))
        | v1_tex_2(X21,X20)
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X20) )
      & ( esk2_2(X20,X21) = u1_struct_0(X21)
        | v1_tex_2(X21,X20)
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ v1_subset_1(esk2_2(X20,X21),u1_struct_0(X20))
        | v1_tex_2(X21,X20)
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( v1_subset_1(k6_domain_1(X1,X2),X1)
    | v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_29,plain,
    ( v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_31,plain,(
    ! [X24,X25] :
      ( ( ~ v1_subset_1(X25,X24)
        | X25 != X24
        | ~ m1_subset_1(X25,k1_zfmisc_1(X24)) )
      & ( X25 = X24
        | v1_subset_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_32,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_33,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_34,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X16)
      | m1_subset_1(u1_struct_0(X17),k1_zfmisc_1(u1_struct_0(X16))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_35,plain,(
    ! [X12] :
      ( v2_struct_0(X12)
      | ~ l1_struct_0(X12)
      | ~ v1_xboole_0(u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_36,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_37,plain,(
    ! [X13] :
      ( ~ v7_struct_0(X13)
      | ~ l1_struct_0(X13)
      | v1_zfmisc_1(u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,esk4_0)) = u1_struct_0(esk3_0)
    | v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | l1_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_41,plain,(
    ! [X26,X27] :
      ( ( ~ v2_struct_0(k1_tex_2(X26,X27))
        | v2_struct_0(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26)) )
      & ( v1_pre_topc(k1_tex_2(X26,X27))
        | v2_struct_0(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26)) )
      & ( m1_pre_topc(k1_tex_2(X26,X27),X26)
        | v2_struct_0(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,esk4_0)) = u1_struct_0(esk3_0)
    | v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_30])])).

fof(c_0_47,plain,(
    ! [X28,X29] :
      ( ( ~ v2_struct_0(k1_tex_2(X28,X29))
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28)) )
      & ( v7_struct_0(k1_tex_2(X28,X29))
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28)) )
      & ( v1_pre_topc(k1_tex_2(X28,X29))
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_48,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_50,plain,(
    ! [X18,X19] :
      ( v1_xboole_0(X18)
      | ~ v1_zfmisc_1(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ v1_subset_1(X19,X18)
      | v1_xboole_0(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_tex_2])])])])).

fof(c_0_51,plain,(
    ! [X5,X6] :
      ( ~ v1_xboole_0(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | v1_xboole_0(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_52,plain,(
    ! [X32,X33] :
      ( v1_xboole_0(X32)
      | ~ m1_subset_1(X33,X32)
      | ~ v1_subset_1(k6_domain_1(X32,X33),X32)
      | ~ v1_zfmisc_1(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).

cnf(c_0_53,negated_conjecture,
    ( ~ l1_struct_0(esk3_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ v7_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_60,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | u1_struct_0(X31) != u1_struct_0(X30)
      | ~ v1_tex_2(X31,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_tex_2])])])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_64,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_30]),c_0_25])]),c_0_42])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_57])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_zfmisc_1(X2) ),
    inference(csr,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | u1_struct_0(X2) != u1_struct_0(X1)
    | ~ v1_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_zfmisc_1(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_25])]),c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_30]),c_0_25])]),c_0_42])).

cnf(c_0_70,plain,
    ( X1 = X2
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_zfmisc_1(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_33])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,esk4_0)) != u1_struct_0(esk3_0)
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_zfmisc_1(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_30])])).

cnf(c_0_73,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_49]),c_0_30]),c_0_25])]),c_0_42])).

cnf(c_0_74,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_zfmisc_1(u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_39])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_43]),c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,esk4_0)) != u1_struct_0(esk3_0)
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_77,plain,
    ( u1_struct_0(k1_tex_2(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_49]),c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_30]),c_0_25]),c_0_73])]),c_0_42])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_49]),c_0_30]),c_0_25])]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 0.13/0.38  fof(t7_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 0.13/0.38  fof(cc1_zfmisc_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 0.13/0.38  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.13/0.38  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.13/0.38  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.13/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.13/0.38  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.13/0.38  fof(cc1_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tex_2)).
% 0.13/0.38  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.13/0.38  fof(t6_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.13/0.38  fof(t15_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>~((u1_struct_0(X2)=u1_struct_0(X1)&v1_tex_2(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 0.13/0.38  fof(c_0_16, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.13/0.38  fof(c_0_17, plain, ![X34, X35]:(v1_xboole_0(X34)|v1_zfmisc_1(X34)|(~m1_subset_1(X35,X34)|v1_subset_1(k6_domain_1(X34,X35),X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).
% 0.13/0.38  fof(c_0_18, plain, ![X4]:(~v1_xboole_0(X4)|v1_zfmisc_1(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).
% 0.13/0.38  fof(c_0_19, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&((~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)))&(v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.13/0.38  cnf(c_0_20, plain, (v1_xboole_0(X1)|v1_zfmisc_1(X1)|v1_subset_1(k6_domain_1(X1,X2),X1)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_21, plain, (v1_zfmisc_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_22, plain, ![X20, X21, X22]:((~v1_tex_2(X21,X20)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(X22!=u1_struct_0(X21)|v1_subset_1(X22,u1_struct_0(X20))))|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))&((m1_subset_1(esk2_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))|v1_tex_2(X21,X20)|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))&((esk2_2(X20,X21)=u1_struct_0(X21)|v1_tex_2(X21,X20)|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))&(~v1_subset_1(esk2_2(X20,X21),u1_struct_0(X20))|v1_tex_2(X21,X20)|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_24, plain, (v1_subset_1(k6_domain_1(X1,X2),X1)|v1_zfmisc_1(X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_26, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_27, plain, (esk2_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.13/0.38  cnf(c_0_29, plain, (v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_31, plain, ![X24, X25]:((~v1_subset_1(X25,X24)|X25!=X24|~m1_subset_1(X25,k1_zfmisc_1(X24)))&(X25=X24|v1_subset_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.13/0.38  cnf(c_0_33, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  fof(c_0_34, plain, ![X16, X17]:(~l1_pre_topc(X16)|(~m1_pre_topc(X17,X16)|m1_subset_1(u1_struct_0(X17),k1_zfmisc_1(u1_struct_0(X16))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.13/0.38  fof(c_0_35, plain, ![X12]:(v2_struct_0(X12)|~l1_struct_0(X12)|~v1_xboole_0(u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.38  fof(c_0_36, plain, ![X9]:(~l1_pre_topc(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  fof(c_0_37, plain, ![X13]:(~v7_struct_0(X13)|~l1_struct_0(X13)|v1_zfmisc_1(u1_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,esk4_0))=u1_struct_0(esk3_0)|v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~m1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.38  cnf(c_0_39, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  fof(c_0_40, plain, ![X10, X11]:(~l1_pre_topc(X10)|(~m1_pre_topc(X11,X10)|l1_pre_topc(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  fof(c_0_41, plain, ![X26, X27]:(((~v2_struct_0(k1_tex_2(X26,X27))|(v2_struct_0(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,u1_struct_0(X26))))&(v1_pre_topc(k1_tex_2(X26,X27))|(v2_struct_0(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,u1_struct_0(X26)))))&(m1_pre_topc(k1_tex_2(X26,X27),X26)|(v2_struct_0(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,u1_struct_0(X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_43, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_44, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_45, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,esk4_0))=u1_struct_0(esk3_0)|v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_30])])).
% 0.13/0.38  fof(c_0_47, plain, ![X28, X29]:(((~v2_struct_0(k1_tex_2(X28,X29))|(v2_struct_0(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,u1_struct_0(X28))))&(v7_struct_0(k1_tex_2(X28,X29))|(v2_struct_0(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,u1_struct_0(X28)))))&(v1_pre_topc(k1_tex_2(X28,X29))|(v2_struct_0(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,u1_struct_0(X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.13/0.38  cnf(c_0_48, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_49, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  fof(c_0_50, plain, ![X18, X19]:(v1_xboole_0(X18)|~v1_zfmisc_1(X18)|(~m1_subset_1(X19,k1_zfmisc_1(X18))|(~v1_subset_1(X19,X18)|v1_xboole_0(X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_tex_2])])])])).
% 0.13/0.38  fof(c_0_51, plain, ![X5, X6]:(~v1_xboole_0(X5)|(~m1_subset_1(X6,k1_zfmisc_1(X5))|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.13/0.38  fof(c_0_52, plain, ![X32, X33]:(v1_xboole_0(X32)|(~m1_subset_1(X33,X32)|(~v1_subset_1(k6_domain_1(X32,X33),X32)|~v1_zfmisc_1(X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (~l1_struct_0(esk3_0)|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_30])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~v7_struct_0(k1_tex_2(esk3_0,esk4_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.38  cnf(c_0_56, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.38  cnf(c_0_57, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_58, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.38  cnf(c_0_59, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.38  fof(c_0_60, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|(u1_struct_0(X31)!=u1_struct_0(X30)|~v1_tex_2(X31,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_tex_2])])])).
% 0.13/0.38  cnf(c_0_61, plain, (v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~v1_subset_1(k6_domain_1(X1,X2),X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_30]), c_0_25])]), c_0_42])).
% 0.13/0.38  cnf(c_0_65, plain, (v2_struct_0(X1)|l1_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_44, c_0_57])).
% 0.13/0.38  cnf(c_0_66, plain, (v1_xboole_0(X1)|~v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_zfmisc_1(X2)), inference(csr,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.38  cnf(c_0_67, plain, (~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|u1_struct_0(X2)!=u1_struct_0(X1)|~v1_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_zfmisc_1(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_25])]), c_0_63])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_30]), c_0_25])]), c_0_42])).
% 0.13/0.38  cnf(c_0_70, plain, (X1=X2|v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_zfmisc_1(X2)), inference(spm,[status(thm)],[c_0_66, c_0_33])).
% 0.13/0.38  cnf(c_0_71, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,esk4_0))!=u1_struct_0(esk3_0)|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_zfmisc_1(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_30])])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_49]), c_0_30]), c_0_25])]), c_0_42])).
% 0.13/0.38  cnf(c_0_74, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_xboole_0(u1_struct_0(X1))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v1_zfmisc_1(u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_70, c_0_39])).
% 0.13/0.38  cnf(c_0_75, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_43]), c_0_65])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,esk4_0))!=u1_struct_0(esk3_0)|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])])).
% 0.13/0.38  cnf(c_0_77, plain, (u1_struct_0(k1_tex_2(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_zfmisc_1(u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_49]), c_0_75])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_30]), c_0_25]), c_0_73])]), c_0_42])).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_49]), c_0_30]), c_0_25])]), c_0_42]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 80
% 0.13/0.38  # Proof object clause steps            : 47
% 0.13/0.38  # Proof object formula steps           : 33
% 0.13/0.38  # Proof object conjectures             : 24
% 0.13/0.38  # Proof object clause conjectures      : 21
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 22
% 0.13/0.38  # Proof object initial formulas used   : 16
% 0.13/0.38  # Proof object generating inferences   : 21
% 0.13/0.38  # Proof object simplifying inferences  : 40
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 18
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 32
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 32
% 0.13/0.38  # Processed clauses                    : 154
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 29
% 0.13/0.38  # ...remaining for further processing  : 125
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 14
% 0.13/0.38  # Backward-rewritten                   : 10
% 0.13/0.38  # Generated clauses                    : 163
% 0.13/0.38  # ...of the previous two non-trivial   : 150
% 0.13/0.38  # Contextual simplify-reflections      : 11
% 0.13/0.38  # Paramodulations                      : 161
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 69
% 0.13/0.38  #    Positive orientable unit clauses  : 6
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 59
% 0.13/0.38  # Current number of unprocessed clauses: 46
% 0.13/0.38  # ...number of literals in the above   : 294
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 54
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1109
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 508
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 47
% 0.13/0.38  # Unit Clause-clause subsumption calls : 11
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6241
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.039 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.042 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
