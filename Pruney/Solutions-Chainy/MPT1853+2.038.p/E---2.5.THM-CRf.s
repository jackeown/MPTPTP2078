%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:30 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 461 expanded)
%              Number of clauses        :   52 ( 171 expanded)
%              Number of leaves         :   14 ( 114 expanded)
%              Depth                    :   23
%              Number of atoms          :  311 (2114 expanded)
%              Number of equality atoms :   23 (  53 expanded)
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

fof(t8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
              & v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(t15_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ~ ( u1_struct_0(X2) = u1_struct_0(X1)
              & v1_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_15,plain,(
    ! [X29,X30] :
      ( v1_xboole_0(X29)
      | v1_zfmisc_1(X29)
      | ~ m1_subset_1(X30,X29)
      | v1_subset_1(k6_domain_1(X29,X30),X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).

fof(c_0_16,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | v1_zfmisc_1(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).

fof(c_0_17,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v1_tex_2(X16,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | X17 != u1_struct_0(X16)
        | v1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk1_2(X15,X16),k1_zfmisc_1(u1_struct_0(X15)))
        | v1_tex_2(X16,X15)
        | ~ m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X15) )
      & ( esk1_2(X15,X16) = u1_struct_0(X16)
        | v1_tex_2(X16,X15)
        | ~ m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ v1_subset_1(esk1_2(X15,X16),u1_struct_0(X15))
        | v1_tex_2(X16,X15)
        | ~ m1_pre_topc(X16,X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_18,plain,(
    ! [X19,X20] :
      ( ( ~ v1_subset_1(X20,X19)
        | X20 != X19
        | ~ m1_subset_1(X20,k1_zfmisc_1(X19)) )
      & ( X20 = X19
        | v1_subset_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ( ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) )
    & ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_subset_1(k6_domain_1(X1,X2),X1)
    | v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X1)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_30,plain,(
    ! [X31,X32] :
      ( v2_struct_0(X31)
      | ~ l1_struct_0(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X31),X32),u1_struct_0(X31))
      | ~ v7_struct_0(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

cnf(c_0_31,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_32,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,esk3_0)) = u1_struct_0(esk2_0)
    | v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

fof(c_0_36,plain,(
    ! [X21,X22] :
      ( ( ~ v2_struct_0(k1_tex_2(X21,X22))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21)) )
      & ( v1_pre_topc(k1_tex_2(X21,X22))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21)) )
      & ( m1_pre_topc(k1_tex_2(X21,X22),X21)
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

cnf(c_0_37,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk2_0,esk3_0))
    | v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_26])).

fof(c_0_38,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | l1_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_39,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_40,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | l1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk2_0,esk3_0))
    | v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_44,plain,(
    ! [X23,X24] :
      ( ( ~ v2_struct_0(k1_tex_2(X23,X24))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) )
      & ( v7_struct_0(k1_tex_2(X23,X24))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) )
      & ( v1_pre_topc(k1_tex_2(X23,X24))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_45,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_47,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | r1_tarski(u1_struct_0(X14),u1_struct_0(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_27]),c_0_33])]),c_0_43])).

cnf(c_0_51,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_53,plain,(
    ! [X27,X28] :
      ( v1_xboole_0(X27)
      | v1_xboole_0(X28)
      | ~ v1_zfmisc_1(X28)
      | ~ r1_tarski(X27,X28)
      | X27 = X28 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_54,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( ~ l1_struct_0(esk2_0)
    | ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_33])).

cnf(c_0_57,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_27]),c_0_33])]),c_0_43])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_52])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_62,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_27]),c_0_33])]),c_0_43])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk2_0)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ v1_zfmisc_1(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_46]),c_0_27]),c_0_33])]),c_0_43])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk2_0)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,X1)) = u1_struct_0(esk2_0)
    | v1_xboole_0(u1_struct_0(k1_tex_2(esk2_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_46]),c_0_33])]),c_0_43])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,X1)) = u1_struct_0(esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ l1_struct_0(k1_tex_2(esk2_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_33])]),c_0_43])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk2_0,X1))
    | ~ v7_struct_0(k1_tex_2(esk2_0,X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),X2),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ l1_struct_0(k1_tex_2(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_71,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | v2_struct_0(k1_tex_2(esk2_0,X1))
    | ~ v7_struct_0(k1_tex_2(esk2_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ l1_struct_0(k1_tex_2(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_27])])).

fof(c_0_72,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_pre_topc(X26,X25)
      | u1_struct_0(X26) != u1_struct_0(X25)
      | ~ v1_tex_2(X26,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_tex_2])])])).

cnf(c_0_73,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | v2_struct_0(k1_tex_2(esk2_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ l1_struct_0(k1_tex_2(esk2_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_51]),c_0_33])]),c_0_43])).

cnf(c_0_74,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | u1_struct_0(X2) != u1_struct_0(X1)
    | ~ v1_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | v2_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_27])).

cnf(c_0_76,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk2_0,esk3_0))
    | u1_struct_0(k1_tex_2(esk2_0,esk3_0)) != u1_struct_0(esk2_0)
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_33])])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,esk3_0)) != u1_struct_0(esk2_0)
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_76]),c_0_27]),c_0_33])]),c_0_43])).

cnf(c_0_78,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_68]),c_0_27])])).

cnf(c_0_79,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_58]),c_0_27]),c_0_33])]),c_0_43])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_46]),c_0_27]),c_0_33])]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 0.13/0.39  fof(t7_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 0.13/0.39  fof(cc1_zfmisc_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 0.13/0.39  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.13/0.39  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.13/0.39  fof(t8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~((v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))&v7_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 0.13/0.39  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.13/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.39  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.13/0.39  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.13/0.39  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.13/0.39  fof(t15_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>~((u1_struct_0(X2)=u1_struct_0(X1)&v1_tex_2(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 0.13/0.39  fof(c_0_14, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.13/0.39  fof(c_0_15, plain, ![X29, X30]:(v1_xboole_0(X29)|v1_zfmisc_1(X29)|(~m1_subset_1(X30,X29)|v1_subset_1(k6_domain_1(X29,X30),X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).
% 0.13/0.39  fof(c_0_16, plain, ![X5]:(~v1_xboole_0(X5)|v1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).
% 0.13/0.39  fof(c_0_17, plain, ![X15, X16, X17]:((~v1_tex_2(X16,X15)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|(X17!=u1_struct_0(X16)|v1_subset_1(X17,u1_struct_0(X15))))|~m1_pre_topc(X16,X15)|~l1_pre_topc(X15))&((m1_subset_1(esk1_2(X15,X16),k1_zfmisc_1(u1_struct_0(X15)))|v1_tex_2(X16,X15)|~m1_pre_topc(X16,X15)|~l1_pre_topc(X15))&((esk1_2(X15,X16)=u1_struct_0(X16)|v1_tex_2(X16,X15)|~m1_pre_topc(X16,X15)|~l1_pre_topc(X15))&(~v1_subset_1(esk1_2(X15,X16),u1_struct_0(X15))|v1_tex_2(X16,X15)|~m1_pre_topc(X16,X15)|~l1_pre_topc(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.13/0.39  fof(c_0_18, plain, ![X19, X20]:((~v1_subset_1(X20,X19)|X20!=X19|~m1_subset_1(X20,k1_zfmisc_1(X19)))&(X20=X19|v1_subset_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.13/0.39  fof(c_0_19, negated_conjecture, ((~v2_struct_0(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&((~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)))&(v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.13/0.39  cnf(c_0_20, plain, (v1_xboole_0(X1)|v1_zfmisc_1(X1)|v1_subset_1(k6_domain_1(X1,X2),X1)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_21, plain, (v1_zfmisc_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_22, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_23, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_24, plain, (m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_26, plain, (v1_subset_1(k6_domain_1(X1,X2),X1)|v1_zfmisc_1(X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_28, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_29, plain, (esk1_2(X1,X2)=u1_struct_0(X1)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.13/0.39  fof(c_0_30, plain, ![X31, X32]:(v2_struct_0(X31)|~l1_struct_0(X31)|(~m1_subset_1(X32,u1_struct_0(X31))|(~v1_subset_1(k6_domain_1(u1_struct_0(X31),X32),u1_struct_0(X31))|~v7_struct_0(X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.13/0.39  cnf(c_0_32, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_34, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~v7_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,esk3_0))=u1_struct_0(esk2_0)|v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.13/0.39  fof(c_0_36, plain, ![X21, X22]:(((~v2_struct_0(k1_tex_2(X21,X22))|(v2_struct_0(X21)|~l1_pre_topc(X21)|~m1_subset_1(X22,u1_struct_0(X21))))&(v1_pre_topc(k1_tex_2(X21,X22))|(v2_struct_0(X21)|~l1_pre_topc(X21)|~m1_subset_1(X22,u1_struct_0(X21)))))&(m1_pre_topc(k1_tex_2(X21,X22),X21)|(v2_struct_0(X21)|~l1_pre_topc(X21)|~m1_subset_1(X22,u1_struct_0(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (v2_struct_0(k1_tex_2(esk2_0,esk3_0))|v1_zfmisc_1(u1_struct_0(esk2_0))|~v7_struct_0(k1_tex_2(esk2_0,esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_26])).
% 0.13/0.39  fof(c_0_38, plain, ![X7, X8]:(~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|l1_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.39  fof(c_0_39, plain, ![X10]:(v2_struct_0(X10)|~l1_struct_0(X10)|~v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.39  fof(c_0_40, plain, ![X6]:(~l1_pre_topc(X6)|l1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.39  cnf(c_0_41, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (v2_struct_0(k1_tex_2(esk2_0,esk3_0))|v1_zfmisc_1(u1_struct_0(esk2_0))|~v7_struct_0(k1_tex_2(esk2_0,esk3_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  fof(c_0_44, plain, ![X23, X24]:(((~v2_struct_0(k1_tex_2(X23,X24))|(v2_struct_0(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,u1_struct_0(X23))))&(v7_struct_0(k1_tex_2(X23,X24))|(v2_struct_0(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,u1_struct_0(X23)))))&(v1_pre_topc(k1_tex_2(X23,X24))|(v2_struct_0(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,u1_struct_0(X23))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.13/0.39  cnf(c_0_45, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.39  cnf(c_0_46, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.39  fof(c_0_47, plain, ![X13, X14]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|r1_tarski(u1_struct_0(X14),u1_struct_0(X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.13/0.39  cnf(c_0_48, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.39  cnf(c_0_49, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~v7_struct_0(k1_tex_2(esk2_0,esk3_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_27]), c_0_33])]), c_0_43])).
% 0.13/0.39  cnf(c_0_51, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  cnf(c_0_52, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.39  fof(c_0_53, plain, ![X27, X28]:(v1_xboole_0(X27)|(v1_xboole_0(X28)|~v1_zfmisc_1(X28)|(~r1_tarski(X27,X28)|X27=X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.13/0.39  cnf(c_0_54, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (~l1_struct_0(esk2_0)|~v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_43, c_0_48])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_33])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_27]), c_0_33])]), c_0_43])).
% 0.13/0.39  cnf(c_0_58, plain, (v2_struct_0(X1)|l1_struct_0(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_49, c_0_52])).
% 0.13/0.39  cnf(c_0_59, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk2_0)), inference(spm,[status(thm)],[c_0_54, c_0_33])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_27]), c_0_33])]), c_0_43])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(esk2_0)|v1_xboole_0(u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)|~v1_zfmisc_1(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_46]), c_0_27]), c_0_33])]), c_0_43])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(esk2_0)|v1_xboole_0(u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])])).
% 0.13/0.39  cnf(c_0_66, plain, (v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2)))), inference(spm,[status(thm)],[c_0_41, c_0_48])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,X1))=u1_struct_0(esk2_0)|v1_xboole_0(u1_struct_0(k1_tex_2(esk2_0,X1)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_46]), c_0_33])]), c_0_43])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,X1))=u1_struct_0(esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~l1_struct_0(k1_tex_2(esk2_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_33])]), c_0_43])).
% 0.13/0.39  cnf(c_0_69, negated_conjecture, (v2_struct_0(k1_tex_2(esk2_0,X1))|~v7_struct_0(k1_tex_2(esk2_0,X1))|~v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),X2),u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~l1_struct_0(k1_tex_2(esk2_0,X1))), inference(spm,[status(thm)],[c_0_34, c_0_68])).
% 0.13/0.39  cnf(c_0_70, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v2_struct_0(k1_tex_2(esk2_0,X1))|~v7_struct_0(k1_tex_2(esk2_0,X1))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~l1_struct_0(k1_tex_2(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_27])])).
% 0.13/0.39  fof(c_0_72, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_pre_topc(X26,X25)|(u1_struct_0(X26)!=u1_struct_0(X25)|~v1_tex_2(X26,X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_tex_2])])])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v2_struct_0(k1_tex_2(esk2_0,X1))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~l1_struct_0(k1_tex_2(esk2_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_51]), c_0_33])]), c_0_43])).
% 0.13/0.39  cnf(c_0_74, plain, (~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|u1_struct_0(X2)!=u1_struct_0(X1)|~v1_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v2_struct_0(k1_tex_2(esk2_0,esk3_0))|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_73, c_0_27])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, (v2_struct_0(k1_tex_2(esk2_0,esk3_0))|u1_struct_0(k1_tex_2(esk2_0,esk3_0))!=u1_struct_0(esk2_0)|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_33])])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,esk3_0))!=u1_struct_0(esk2_0)|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_76]), c_0_27]), c_0_33])]), c_0_43])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_68]), c_0_27])])).
% 0.13/0.39  cnf(c_0_79, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_58]), c_0_27]), c_0_33])]), c_0_43])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_46]), c_0_27]), c_0_33])]), c_0_43]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 81
% 0.13/0.39  # Proof object clause steps            : 52
% 0.13/0.39  # Proof object formula steps           : 29
% 0.13/0.39  # Proof object conjectures             : 33
% 0.13/0.39  # Proof object clause conjectures      : 30
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 21
% 0.13/0.39  # Proof object initial formulas used   : 14
% 0.13/0.39  # Proof object generating inferences   : 28
% 0.13/0.39  # Proof object simplifying inferences  : 55
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 17
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 29
% 0.13/0.39  # Removed in clause preprocessing      : 1
% 0.13/0.39  # Initial clauses in saturation        : 28
% 0.13/0.39  # Processed clauses                    : 208
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 49
% 0.13/0.39  # ...remaining for further processing  : 157
% 0.13/0.39  # Other redundant clauses eliminated   : 2
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 29
% 0.13/0.39  # Backward-rewritten                   : 13
% 0.13/0.39  # Generated clauses                    : 274
% 0.13/0.39  # ...of the previous two non-trivial   : 255
% 0.13/0.39  # Contextual simplify-reflections      : 5
% 0.13/0.39  # Paramodulations                      : 272
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 2
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 87
% 0.13/0.39  #    Positive orientable unit clauses  : 6
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 5
% 0.13/0.39  #    Non-unit-clauses                  : 76
% 0.13/0.39  # Current number of unprocessed clauses: 86
% 0.13/0.39  # ...number of literals in the above   : 534
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 69
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1954
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 914
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 69
% 0.13/0.39  # Unit Clause-clause subsumption calls : 79
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 4
% 0.13/0.39  # BW rewrite match successes           : 4
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 8679
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.044 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.047 s
% 0.13/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
