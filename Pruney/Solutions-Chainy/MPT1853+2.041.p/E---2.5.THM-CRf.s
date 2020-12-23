%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:31 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 617 expanded)
%              Number of clauses        :   60 ( 233 expanded)
%              Number of leaves         :   15 ( 153 expanded)
%              Depth                    :   18
%              Number of atoms          :  333 (2661 expanded)
%              Number of equality atoms :   24 ( 108 expanded)
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

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t6_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_16,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | l1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ( ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) )
    & ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X24,X25] :
      ( ( ~ v1_subset_1(X25,X24)
        | X25 != X24
        | ~ m1_subset_1(X25,k1_zfmisc_1(X24)) )
      & ( X25 = X24
        | v1_subset_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_19,plain,(
    ! [X9] :
      ( v2_struct_0(X9)
      | ~ l1_struct_0(X9)
      | ~ v1_xboole_0(u1_struct_0(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_20,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X11,X12] :
      ( v1_xboole_0(X11)
      | ~ m1_subset_1(X12,X11)
      | m1_subset_1(k6_domain_1(X11,X12),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_28,plain,(
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

fof(c_0_29,plain,(
    ! [X17,X19] :
      ( ( m1_subset_1(esk1_1(X17),X17)
        | ~ v1_zfmisc_1(X17)
        | v1_xboole_0(X17) )
      & ( X17 = k6_domain_1(X17,esk1_1(X17))
        | ~ v1_zfmisc_1(X17)
        | v1_xboole_0(X17) )
      & ( ~ m1_subset_1(X19,X17)
        | X17 != k6_domain_1(X17,X19)
        | v1_zfmisc_1(X17)
        | v1_xboole_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

cnf(c_0_30,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),esk4_0) = u1_struct_0(esk3_0)
    | ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_34,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X2 != k6_domain_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),esk4_0) = u1_struct_0(esk3_0)
    | ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_38,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X1)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_23]),c_0_35])).

fof(c_0_40,plain,(
    ! [X10] :
      ( ~ v7_struct_0(X10)
      | ~ l1_struct_0(X10)
      | v1_zfmisc_1(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_41,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_32])]),c_0_33])).

cnf(c_0_42,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_43,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | l1_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_44,plain,(
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

fof(c_0_45,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ v1_zfmisc_1(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_xboole_0(X16)
      | ~ v1_subset_1(X16,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).

fof(c_0_46,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | ~ v1_subset_1(X5,X4) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).

cnf(c_0_47,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,esk4_0)) = u1_struct_0(esk3_0)
    | v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_21])])).

fof(c_0_49,plain,(
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

cnf(c_0_50,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_54,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | m1_subset_1(u1_struct_0(X14),k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_55,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ v7_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X2)
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_21]),c_0_32])]),c_0_25])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_57])).

fof(c_0_62,plain,(
    ! [X30,X31] :
      ( v1_xboole_0(X30)
      | ~ m1_subset_1(X31,X30)
      | ~ v1_subset_1(k6_domain_1(X30,X31),X30)
      | ~ v1_zfmisc_1(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).

cnf(c_0_63,plain,
    ( X1 = X2
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_23])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_21])).

cnf(c_0_65,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_21]),c_0_32])]),c_0_25])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_37])).

cnf(c_0_67,plain,
    ( v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_38])).

cnf(c_0_68,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_70,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk3_0)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_51]),c_0_21]),c_0_32])]),c_0_25])).

cnf(c_0_73,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))
    | ~ v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_21])])).

cnf(c_0_74,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v1_zfmisc_1(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_32])])).

cnf(c_0_75,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_70]),c_0_59])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk3_0)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_78,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_67]),c_0_21])])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,esk4_0)) = u1_struct_0(esk3_0)
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_23]),c_0_64])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_74]),c_0_33])).

cnf(c_0_81,negated_conjecture,
    ( v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))
    | ~ v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_74]),c_0_21])]),c_0_33])).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_26])).

cnf(c_0_83,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,X1)) = u1_struct_0(esk3_0)
    | v1_xboole_0(u1_struct_0(k1_tex_2(esk3_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_51]),c_0_21])]),c_0_25])).

cnf(c_0_84,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_72])])).

cnf(c_0_86,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,X1)) = u1_struct_0(esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_21])]),c_0_25])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_51]),c_0_21]),c_0_32])]),c_0_25])).

cnf(c_0_88,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_32])]),c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_61]),c_0_21]),c_0_32])]),c_0_25])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_51]),c_0_21]),c_0_32])]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:19:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
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
% 0.13/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.39  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.13/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.39  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.13/0.39  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.13/0.39  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 0.13/0.39  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.13/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.39  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.13/0.39  fof(cc2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_xboole_0(X2))=>~(v1_subset_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 0.13/0.39  fof(cc4_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~(v1_subset_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 0.13/0.39  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.13/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.13/0.39  fof(t6_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.13/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.13/0.39  fof(c_0_16, plain, ![X6]:(~l1_pre_topc(X6)|l1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.39  fof(c_0_17, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&((~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)))&(v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.13/0.39  fof(c_0_18, plain, ![X24, X25]:((~v1_subset_1(X25,X24)|X25!=X24|~m1_subset_1(X25,k1_zfmisc_1(X24)))&(X25=X24|v1_subset_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.13/0.39  fof(c_0_19, plain, ![X9]:(v2_struct_0(X9)|~l1_struct_0(X9)|~v1_xboole_0(u1_struct_0(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.39  cnf(c_0_20, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_23, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  fof(c_0_24, plain, ![X11, X12]:(v1_xboole_0(X11)|~m1_subset_1(X12,X11)|m1_subset_1(k6_domain_1(X11,X12),k1_zfmisc_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_26, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.39  fof(c_0_28, plain, ![X20, X21, X22]:((~v1_tex_2(X21,X20)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(X22!=u1_struct_0(X21)|v1_subset_1(X22,u1_struct_0(X20))))|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))&((m1_subset_1(esk2_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))|v1_tex_2(X21,X20)|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))&((esk2_2(X20,X21)=u1_struct_0(X21)|v1_tex_2(X21,X20)|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))&(~v1_subset_1(esk2_2(X20,X21),u1_struct_0(X20))|v1_tex_2(X21,X20)|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.13/0.39  fof(c_0_29, plain, ![X17, X19]:(((m1_subset_1(esk1_1(X17),X17)|~v1_zfmisc_1(X17)|v1_xboole_0(X17))&(X17=k6_domain_1(X17,esk1_1(X17))|~v1_zfmisc_1(X17)|v1_xboole_0(X17)))&(~m1_subset_1(X19,X17)|X17!=k6_domain_1(X17,X19)|v1_zfmisc_1(X17)|v1_xboole_0(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),esk4_0)=u1_struct_0(esk3_0)|~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.39  cnf(c_0_31, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.13/0.39  cnf(c_0_34, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_35, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_36, plain, (v1_zfmisc_1(X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)|X2!=k6_domain_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),esk4_0)=u1_struct_0(esk3_0)|~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])]), c_0_33])).
% 0.13/0.39  cnf(c_0_38, plain, (esk2_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_39, plain, (esk2_2(X1,X2)=u1_struct_0(X1)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_23]), c_0_35])).
% 0.13/0.39  fof(c_0_40, plain, ![X10]:(~v7_struct_0(X10)|~l1_struct_0(X10)|v1_zfmisc_1(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_32])]), c_0_33])).
% 0.13/0.39  cnf(c_0_42, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.39  fof(c_0_43, plain, ![X7, X8]:(~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|l1_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.39  fof(c_0_44, plain, ![X26, X27]:(((~v2_struct_0(k1_tex_2(X26,X27))|(v2_struct_0(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,u1_struct_0(X26))))&(v1_pre_topc(k1_tex_2(X26,X27))|(v2_struct_0(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,u1_struct_0(X26)))))&(m1_pre_topc(k1_tex_2(X26,X27),X26)|(v2_struct_0(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,u1_struct_0(X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.13/0.39  fof(c_0_45, plain, ![X15, X16]:(v1_xboole_0(X15)|~v1_zfmisc_1(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|(v1_xboole_0(X16)|~v1_subset_1(X16,X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).
% 0.13/0.39  fof(c_0_46, plain, ![X4, X5]:(~v1_xboole_0(X4)|(~m1_subset_1(X5,k1_zfmisc_1(X4))|~v1_subset_1(X5,X4))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).
% 0.13/0.39  cnf(c_0_47, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,esk4_0))=u1_struct_0(esk3_0)|v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_21])])).
% 0.13/0.39  fof(c_0_49, plain, ![X28, X29]:(((~v2_struct_0(k1_tex_2(X28,X29))|(v2_struct_0(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,u1_struct_0(X28))))&(v7_struct_0(k1_tex_2(X28,X29))|(v2_struct_0(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,u1_struct_0(X28)))))&(v1_pre_topc(k1_tex_2(X28,X29))|(v2_struct_0(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,u1_struct_0(X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.13/0.39  cnf(c_0_50, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_51, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  cnf(c_0_52, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.39  cnf(c_0_53, plain, (~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.39  fof(c_0_54, plain, ![X13, X14]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|m1_subset_1(u1_struct_0(X14),k1_zfmisc_1(u1_struct_0(X13))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~v7_struct_0(k1_tex_2(esk3_0,esk4_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.39  cnf(c_0_56, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.39  cnf(c_0_57, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.39  cnf(c_0_58, plain, (v1_xboole_0(X1)|~v1_zfmisc_1(X2)|~v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.39  cnf(c_0_59, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_21]), c_0_32])]), c_0_25])).
% 0.13/0.39  cnf(c_0_61, plain, (v2_struct_0(X1)|l1_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_20, c_0_57])).
% 0.13/0.39  fof(c_0_62, plain, ![X30, X31]:(v1_xboole_0(X30)|(~m1_subset_1(X31,X30)|(~v1_subset_1(k6_domain_1(X30,X31),X30)|~v1_zfmisc_1(X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).
% 0.13/0.39  cnf(c_0_63, plain, (X1=X2|v1_xboole_0(X1)|~v1_zfmisc_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_58, c_0_23])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_pre_topc(X1,esk3_0)), inference(spm,[status(thm)],[c_0_59, c_0_21])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_21]), c_0_32])]), c_0_25])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_22, c_0_37])).
% 0.13/0.39  cnf(c_0_67, plain, (v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_34, c_0_38])).
% 0.13/0.39  cnf(c_0_68, plain, (v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~v1_subset_1(k6_domain_1(X1,X2),X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.39  cnf(c_0_69, negated_conjecture, (v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_70, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(esk3_0)|v1_xboole_0(u1_struct_0(X1))|~v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(X1,esk3_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_51]), c_0_21]), c_0_32])]), c_0_25])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))|~v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_21])])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|v1_xboole_0(u1_struct_0(esk3_0))|~v1_zfmisc_1(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_32])])).
% 0.13/0.39  cnf(c_0_75, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_70]), c_0_59])).
% 0.13/0.39  cnf(c_0_76, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(esk3_0)|v1_xboole_0(u1_struct_0(X1))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72])])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_67]), c_0_21])])).
% 0.13/0.39  cnf(c_0_79, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,esk4_0))=u1_struct_0(esk3_0)|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_23]), c_0_64])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (~v1_zfmisc_1(u1_struct_0(esk3_0))|~v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_74]), c_0_33])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))|~v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_74]), c_0_21])]), c_0_33])).
% 0.13/0.39  cnf(c_0_82, plain, (v2_struct_0(X1)|~l1_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2)))), inference(spm,[status(thm)],[c_0_76, c_0_26])).
% 0.13/0.39  cnf(c_0_83, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,X1))=u1_struct_0(esk3_0)|v1_xboole_0(u1_struct_0(k1_tex_2(esk3_0,X1)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_51]), c_0_21])]), c_0_25])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.13/0.39  cnf(c_0_85, negated_conjecture, (v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_72])])).
% 0.13/0.39  cnf(c_0_86, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,X1))=u1_struct_0(esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,X1))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_21])]), c_0_25])).
% 0.13/0.39  cnf(c_0_87, negated_conjecture, (~v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_51]), c_0_21]), c_0_32])]), c_0_25])).
% 0.13/0.39  cnf(c_0_88, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_32])]), c_0_87])).
% 0.13/0.39  cnf(c_0_89, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_61]), c_0_21]), c_0_32])]), c_0_25])).
% 0.13/0.39  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_51]), c_0_21]), c_0_32])]), c_0_25]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 91
% 0.13/0.39  # Proof object clause steps            : 60
% 0.13/0.39  # Proof object formula steps           : 31
% 0.13/0.39  # Proof object conjectures             : 36
% 0.13/0.39  # Proof object clause conjectures      : 33
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 23
% 0.13/0.39  # Proof object initial formulas used   : 15
% 0.13/0.39  # Proof object generating inferences   : 33
% 0.13/0.39  # Proof object simplifying inferences  : 63
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 15
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 29
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 29
% 0.13/0.39  # Processed clauses                    : 154
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 31
% 0.13/0.39  # ...remaining for further processing  : 122
% 0.13/0.39  # Other redundant clauses eliminated   : 2
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 20
% 0.13/0.39  # Backward-rewritten                   : 12
% 0.13/0.39  # Generated clauses                    : 175
% 0.13/0.39  # ...of the previous two non-trivial   : 160
% 0.13/0.39  # Contextual simplify-reflections      : 8
% 0.13/0.39  # Paramodulations                      : 173
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
% 0.13/0.39  # Current number of processed clauses  : 61
% 0.13/0.39  #    Positive orientable unit clauses  : 7
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 4
% 0.13/0.39  #    Non-unit-clauses                  : 50
% 0.13/0.39  # Current number of unprocessed clauses: 38
% 0.13/0.39  # ...number of literals in the above   : 206
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 59
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 808
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 427
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 43
% 0.13/0.39  # Unit Clause-clause subsumption calls : 26
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 3
% 0.13/0.39  # BW rewrite match successes           : 3
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 6433
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.036 s
% 0.13/0.39  # System time              : 0.006 s
% 0.13/0.39  # Total time               : 0.042 s
% 0.13/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
