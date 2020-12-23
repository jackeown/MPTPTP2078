%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:30 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 398 expanded)
%              Number of clauses        :   61 ( 151 expanded)
%              Number of leaves         :   17 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  352 (1765 expanded)
%              Number of equality atoms :   25 (  77 expanded)
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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(cc2_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_xboole_0(X2)
           => ~ v1_subset_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(cc4_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ~ v1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

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

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(cc1_zfmisc_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_zfmisc_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

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

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(fc6_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_18,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ( ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) )
    & ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_20,plain,(
    ! [X17,X18] :
      ( v1_xboole_0(X17)
      | ~ v1_zfmisc_1(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | v1_xboole_0(X18)
      | ~ v1_subset_1(X18,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).

fof(c_0_21,plain,(
    ! [X5,X6] :
      ( ~ v1_xboole_0(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ v1_subset_1(X6,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).

fof(c_0_22,plain,(
    ! [X26,X27] :
      ( ( ~ v1_subset_1(X27,X26)
        | X27 != X26
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26)) )
      & ( X27 = X26
        | v1_subset_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_23,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_24,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | m1_subset_1(u1_struct_0(X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X13,X14] :
      ( v1_xboole_0(X13)
      | ~ m1_subset_1(X14,X13)
      | m1_subset_1(k6_domain_1(X13,X14),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_35,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v1_tex_2(X23,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | X24 != u1_struct_0(X23)
        | v1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk2_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))
        | v1_tex_2(X23,X22)
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) )
      & ( esk2_2(X22,X23) = u1_struct_0(X23)
        | v1_tex_2(X23,X22)
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ v1_subset_1(esk2_2(X22,X23),u1_struct_0(X22))
        | v1_tex_2(X23,X22)
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_36,plain,(
    ! [X19,X21] :
      ( ( m1_subset_1(esk1_1(X19),X19)
        | ~ v1_zfmisc_1(X19)
        | v1_xboole_0(X19) )
      & ( X19 = k6_domain_1(X19,esk1_1(X19))
        | ~ v1_zfmisc_1(X19)
        | v1_xboole_0(X19) )
      & ( ~ m1_subset_1(X21,X19)
        | X19 != k6_domain_1(X19,X21)
        | v1_zfmisc_1(X19)
        | v1_xboole_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

fof(c_0_37,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | v1_zfmisc_1(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_zfmisc_1(X2) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_39,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),esk4_0) = u1_struct_0(esk3_0)
    | ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_44,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X2 != k6_domain_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( X1 = X2
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_zfmisc_1(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_30])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

fof(c_0_50,plain,(
    ! [X12] :
      ( ~ v7_struct_0(X12)
      | ~ l1_struct_0(X12)
      | v1_zfmisc_1(u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_51,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),esk4_0) = u1_struct_0(esk3_0)
    | ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),c_0_43])).

cnf(c_0_52,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_53,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X1)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_30]),c_0_45])).

cnf(c_0_54,plain,
    ( v1_zfmisc_1(X1)
    | k6_domain_1(X1,X2) != X1
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_55,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ l1_struct_0(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X32),X33),u1_struct_0(X32))
      | ~ v7_struct_0(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

fof(c_0_56,plain,(
    ! [X28,X29] :
      ( ( ~ v2_struct_0(k1_tex_2(X28,X29))
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28)) )
      & ( v1_pre_topc(k1_tex_2(X28,X29))
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28)) )
      & ( m1_pre_topc(k1_tex_2(X28,X29),X28)
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

cnf(c_0_57,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk3_0)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ v1_zfmisc_1(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_51])).

cnf(c_0_60,plain,
    ( v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_52])).

cnf(c_0_61,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_42])])).

fof(c_0_63,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | l1_pre_topc(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_64,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk3_0)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v7_struct_0(esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_34])])).

cnf(c_0_69,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))
    | ~ v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_25])])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,esk4_0)) = u1_struct_0(esk3_0)
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_61]),c_0_25])])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,esk4_0)) = u1_struct_0(esk3_0)
    | v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_61]),c_0_25])])).

fof(c_0_73,plain,(
    ! [X30,X31] :
      ( ( ~ v2_struct_0(k1_tex_2(X30,X31))
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30)) )
      & ( v7_struct_0(k1_tex_2(X30,X31))
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30)) )
      & ( v1_pre_topc(k1_tex_2(X30,X31))
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_74,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_64]),c_0_39])).

cnf(c_0_76,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v7_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_42])]),c_0_32]),c_0_34])])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_33])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,X1)) = u1_struct_0(esk3_0)
    | v1_xboole_0(u1_struct_0(k1_tex_2(esk3_0,X1)))
    | ~ v7_struct_0(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_25])]),c_0_32])).

cnf(c_0_79,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ v7_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_72])).

cnf(c_0_81,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_69])).

cnf(c_0_83,negated_conjecture,
    ( v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))
    | ~ v7_struct_0(esk3_0)
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_25])])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,X1)) = u1_struct_0(esk3_0)
    | ~ v7_struct_0(esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_25])]),c_0_32])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_69]),c_0_25]),c_0_42])]),c_0_32])).

cnf(c_0_86,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_25]),c_0_42])]),c_0_32])).

cnf(c_0_87,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( ~ v7_struct_0(esk3_0)
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_42])]),c_0_85])).

fof(c_0_89,plain,(
    ! [X11] :
      ( v7_struct_0(X11)
      | ~ l1_struct_0(X11)
      | ~ v1_zfmisc_1(u1_struct_0(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).

cnf(c_0_90,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_25]),c_0_42])]),c_0_32])).

cnf(c_0_91,negated_conjecture,
    ( ~ v7_struct_0(esk3_0)
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_87]),c_0_25]),c_0_42])]),c_0_32])).

cnf(c_0_92,plain,
    ( v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_69]),c_0_25]),c_0_42])]),c_0_32])).

cnf(c_0_94,negated_conjecture,
    ( ~ v7_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_69]),c_0_25]),c_0_42])]),c_0_32])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_34])]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
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
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(cc2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_xboole_0(X2))=>~(v1_subset_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 0.13/0.38  fof(cc4_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~(v1_subset_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 0.13/0.38  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.13/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.38  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.13/0.38  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.13/0.38  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.13/0.38  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 0.13/0.38  fof(cc1_zfmisc_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 0.13/0.38  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.13/0.38  fof(t8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~((v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))&v7_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 0.13/0.38  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.13/0.38  fof(fc6_struct_0, axiom, ![X1]:((~(v7_struct_0(X1))&l1_struct_0(X1))=>~(v1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 0.13/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.13/0.38  fof(c_0_18, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  fof(c_0_19, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&((~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)))&(v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X17, X18]:(v1_xboole_0(X17)|~v1_zfmisc_1(X17)|(~m1_subset_1(X18,k1_zfmisc_1(X17))|(v1_xboole_0(X18)|~v1_subset_1(X18,X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X5, X6]:(~v1_xboole_0(X5)|(~m1_subset_1(X6,k1_zfmisc_1(X5))|~v1_subset_1(X6,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).
% 0.13/0.38  fof(c_0_22, plain, ![X26, X27]:((~v1_subset_1(X27,X26)|X27!=X26|~m1_subset_1(X27,k1_zfmisc_1(X26)))&(X27=X26|v1_subset_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.13/0.38  fof(c_0_23, plain, ![X10]:(v2_struct_0(X10)|~l1_struct_0(X10)|~v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.38  cnf(c_0_24, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_26, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  fof(c_0_28, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|m1_subset_1(u1_struct_0(X16),k1_zfmisc_1(u1_struct_0(X15))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_30, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  fof(c_0_31, plain, ![X13, X14]:(v1_xboole_0(X13)|~m1_subset_1(X14,X13)|m1_subset_1(k6_domain_1(X13,X14),k1_zfmisc_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_33, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  fof(c_0_35, plain, ![X22, X23, X24]:((~v1_tex_2(X23,X22)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(X24!=u1_struct_0(X23)|v1_subset_1(X24,u1_struct_0(X22))))|~m1_pre_topc(X23,X22)|~l1_pre_topc(X22))&((m1_subset_1(esk2_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))|v1_tex_2(X23,X22)|~m1_pre_topc(X23,X22)|~l1_pre_topc(X22))&((esk2_2(X22,X23)=u1_struct_0(X23)|v1_tex_2(X23,X22)|~m1_pre_topc(X23,X22)|~l1_pre_topc(X22))&(~v1_subset_1(esk2_2(X22,X23),u1_struct_0(X22))|v1_tex_2(X23,X22)|~m1_pre_topc(X23,X22)|~l1_pre_topc(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.13/0.38  fof(c_0_36, plain, ![X19, X21]:(((m1_subset_1(esk1_1(X19),X19)|~v1_zfmisc_1(X19)|v1_xboole_0(X19))&(X19=k6_domain_1(X19,esk1_1(X19))|~v1_zfmisc_1(X19)|v1_xboole_0(X19)))&(~m1_subset_1(X21,X19)|X19!=k6_domain_1(X19,X21)|v1_zfmisc_1(X19)|v1_xboole_0(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.13/0.38  fof(c_0_37, plain, ![X4]:(~v1_xboole_0(X4)|v1_zfmisc_1(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_38, plain, (v1_xboole_0(X1)|~v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_zfmisc_1(X2)), inference(csr,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_39, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),esk4_0)=u1_struct_0(esk3_0)|~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.38  cnf(c_0_41, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.13/0.38  cnf(c_0_44, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_45, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_46, plain, (v1_zfmisc_1(X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)|X2!=k6_domain_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_47, plain, (v1_zfmisc_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_48, plain, (X1=X2|v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_zfmisc_1(X2)), inference(spm,[status(thm)],[c_0_38, c_0_30])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_pre_topc(X1,esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_25])).
% 0.13/0.38  fof(c_0_50, plain, ![X12]:(~v7_struct_0(X12)|~l1_struct_0(X12)|v1_zfmisc_1(u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),esk4_0)=u1_struct_0(esk3_0)|~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])]), c_0_43])).
% 0.13/0.38  cnf(c_0_52, plain, (esk2_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_53, plain, (esk2_2(X1,X2)=u1_struct_0(X1)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_30]), c_0_45])).
% 0.13/0.38  cnf(c_0_54, plain, (v1_zfmisc_1(X1)|k6_domain_1(X1,X2)!=X1|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.38  fof(c_0_55, plain, ![X32, X33]:(v2_struct_0(X32)|~l1_struct_0(X32)|(~m1_subset_1(X33,u1_struct_0(X32))|(~v1_subset_1(k6_domain_1(u1_struct_0(X32),X33),u1_struct_0(X32))|~v7_struct_0(X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).
% 0.13/0.38  fof(c_0_56, plain, ![X28, X29]:(((~v2_struct_0(k1_tex_2(X28,X29))|(v2_struct_0(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,u1_struct_0(X28))))&(v1_pre_topc(k1_tex_2(X28,X29))|(v2_struct_0(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,u1_struct_0(X28)))))&(m1_pre_topc(k1_tex_2(X28,X29),X28)|(v2_struct_0(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,u1_struct_0(X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(esk3_0)|v1_xboole_0(u1_struct_0(X1))|~m1_pre_topc(X1,esk3_0)|~v1_zfmisc_1(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_58, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_51])).
% 0.13/0.38  cnf(c_0_60, plain, (v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_44, c_0_52])).
% 0.13/0.38  cnf(c_0_61, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_42])])).
% 0.13/0.38  fof(c_0_63, plain, ![X8, X9]:(~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|l1_pre_topc(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  cnf(c_0_64, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_65, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~v7_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_67, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(esk3_0)|v1_xboole_0(u1_struct_0(X1))|~v7_struct_0(esk3_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_34])])).
% 0.13/0.38  cnf(c_0_69, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))|~v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_25])])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,esk4_0))=u1_struct_0(esk3_0)|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_61]), c_0_25])])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,esk4_0))=u1_struct_0(esk3_0)|v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_61]), c_0_25])])).
% 0.13/0.38  fof(c_0_73, plain, ![X30, X31]:(((~v2_struct_0(k1_tex_2(X30,X31))|(v2_struct_0(X30)|~l1_pre_topc(X30)|~m1_subset_1(X31,u1_struct_0(X30))))&(v7_struct_0(k1_tex_2(X30,X31))|(v2_struct_0(X30)|~l1_pre_topc(X30)|~m1_subset_1(X31,u1_struct_0(X30)))))&(v1_pre_topc(k1_tex_2(X30,X31))|(v2_struct_0(X30)|~l1_pre_topc(X30)|~m1_subset_1(X31,u1_struct_0(X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.13/0.38  cnf(c_0_74, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.38  cnf(c_0_75, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_64]), c_0_39])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v7_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_42])]), c_0_32]), c_0_34])])).
% 0.13/0.38  cnf(c_0_77, plain, (v2_struct_0(X1)|~l1_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2)))), inference(spm,[status(thm)],[c_0_67, c_0_33])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,X1))=u1_struct_0(esk3_0)|v1_xboole_0(u1_struct_0(k1_tex_2(esk3_0,X1)))|~v7_struct_0(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_25])]), c_0_32])).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.13/0.38  cnf(c_0_80, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~v7_struct_0(k1_tex_2(esk3_0,esk4_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_72])).
% 0.13/0.38  cnf(c_0_81, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.38  cnf(c_0_82, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_74, c_0_69])).
% 0.13/0.38  cnf(c_0_83, negated_conjecture, (v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))|~v7_struct_0(esk3_0)|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_25])])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,X1))=u1_struct_0(esk3_0)|~v7_struct_0(esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,X1))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_25])]), c_0_32])).
% 0.13/0.38  cnf(c_0_85, negated_conjecture, (~v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_69]), c_0_25]), c_0_42])]), c_0_32])).
% 0.13/0.38  cnf(c_0_86, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_25]), c_0_42])]), c_0_32])).
% 0.13/0.38  cnf(c_0_87, plain, (v2_struct_0(X1)|l1_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_24, c_0_82])).
% 0.13/0.38  cnf(c_0_88, negated_conjecture, (~v7_struct_0(esk3_0)|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_42])]), c_0_85])).
% 0.13/0.38  fof(c_0_89, plain, ![X11]:(v7_struct_0(X11)|~l1_struct_0(X11)|~v1_zfmisc_1(u1_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).
% 0.13/0.38  cnf(c_0_90, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_25]), c_0_42])]), c_0_32])).
% 0.13/0.38  cnf(c_0_91, negated_conjecture, (~v7_struct_0(esk3_0)|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_87]), c_0_25]), c_0_42])]), c_0_32])).
% 0.13/0.38  cnf(c_0_92, plain, (v7_struct_0(X1)|~l1_struct_0(X1)|~v1_zfmisc_1(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.13/0.38  cnf(c_0_93, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_69]), c_0_25]), c_0_42])]), c_0_32])).
% 0.13/0.38  cnf(c_0_94, negated_conjecture, (~v7_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_69]), c_0_25]), c_0_42])]), c_0_32])).
% 0.13/0.38  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_34])]), c_0_94]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 96
% 0.13/0.38  # Proof object clause steps            : 61
% 0.13/0.38  # Proof object formula steps           : 35
% 0.13/0.38  # Proof object conjectures             : 34
% 0.13/0.38  # Proof object clause conjectures      : 31
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 25
% 0.13/0.38  # Proof object initial formulas used   : 17
% 0.13/0.38  # Proof object generating inferences   : 33
% 0.13/0.38  # Proof object simplifying inferences  : 63
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 17
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 31
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 31
% 0.13/0.38  # Processed clauses                    : 132
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 19
% 0.13/0.38  # ...remaining for further processing  : 112
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 14
% 0.13/0.38  # Backward-rewritten                   : 6
% 0.13/0.38  # Generated clauses                    : 154
% 0.13/0.38  # ...of the previous two non-trivial   : 144
% 0.13/0.38  # Contextual simplify-reflections      : 7
% 0.13/0.38  # Paramodulations                      : 152
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
% 0.13/0.38  # Current number of processed clauses  : 61
% 0.13/0.38  #    Positive orientable unit clauses  : 5
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 52
% 0.13/0.38  # Current number of unprocessed clauses: 62
% 0.13/0.38  # ...number of literals in the above   : 356
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 49
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 782
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 440
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 30
% 0.13/0.38  # Unit Clause-clause subsumption calls : 42
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6056
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.035 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.041 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
