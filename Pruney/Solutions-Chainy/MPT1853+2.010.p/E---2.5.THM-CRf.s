%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:26 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 191 expanded)
%              Number of clauses        :   41 (  69 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  281 ( 868 expanded)
%              Number of equality atoms :   18 (  28 expanded)
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

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

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

fof(t8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
              & v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(cc10_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v7_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ~ v2_struct_0(X2)
           => ( ~ v2_struct_0(X2)
              & ~ v1_tex_2(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

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

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ( ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) )
    & ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_16,plain,(
    ! [X21,X22] :
      ( ( ~ v1_subset_1(X22,X21)
        | X22 != X21
        | ~ m1_subset_1(X22,k1_zfmisc_1(X21)) )
      & ( X22 = X21
        | v1_subset_1(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_17,plain,(
    ! [X14,X16] :
      ( ( m1_subset_1(esk1_1(X14),X14)
        | ~ v1_zfmisc_1(X14)
        | v1_xboole_0(X14) )
      & ( X14 = k6_domain_1(X14,esk1_1(X14))
        | ~ v1_zfmisc_1(X14)
        | v1_xboole_0(X14) )
      & ( ~ m1_subset_1(X16,X14)
        | X14 != k6_domain_1(X14,X16)
        | v1_zfmisc_1(X14)
        | v1_xboole_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

fof(c_0_18,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | v1_zfmisc_1(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( v1_xboole_0(X10)
      | ~ m1_subset_1(X11,X10)
      | m1_subset_1(k6_domain_1(X10,X11),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_22,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v1_tex_2(X18,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | X19 != u1_struct_0(X18)
        | v1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_pre_topc(X18,X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk2_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))
        | v1_tex_2(X18,X17)
        | ~ m1_pre_topc(X18,X17)
        | ~ l1_pre_topc(X17) )
      & ( esk2_2(X17,X18) = u1_struct_0(X18)
        | v1_tex_2(X18,X17)
        | ~ m1_pre_topc(X18,X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ v1_subset_1(esk2_2(X17,X18),u1_struct_0(X17))
        | v1_tex_2(X18,X17)
        | ~ m1_pre_topc(X18,X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

cnf(c_0_23,plain,
    ( v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X2 != k6_domain_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),esk4_0) = u1_struct_0(esk3_0)
    | ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v1_zfmisc_1(X1)
    | k6_domain_1(X1,X2) != X1
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),esk4_0) = u1_struct_0(esk3_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_32,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X1)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_29])).

fof(c_0_34,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | l1_pre_topc(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_35,plain,(
    ! [X23,X24] :
      ( ( ~ v2_struct_0(k1_tex_2(X23,X24))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) )
      & ( v1_pre_topc(k1_tex_2(X23,X24))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) )
      & ( m1_pre_topc(k1_tex_2(X23,X24),X23)
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_36,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ l1_struct_0(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X27),X28),u1_struct_0(X27))
      | ~ v7_struct_0(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

fof(c_0_37,plain,(
    ! [X9] :
      ( ~ v7_struct_0(X9)
      | ~ l1_struct_0(X9)
      | v1_zfmisc_1(u1_struct_0(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_38,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_27])]),c_0_24])).

cnf(c_0_39,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_41,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | l1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_42,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X12,X13] :
      ( ( ~ v2_struct_0(X13)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X12)
        | ~ v7_struct_0(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ v1_tex_2(X13,X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X12)
        | ~ v7_struct_0(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,esk4_0)) = u1_struct_0(esk3_0)
    | v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_50,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v7_struct_0(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v7_struct_0(esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_27])]),c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ v7_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_56,plain,(
    ! [X25,X26] :
      ( ( ~ v2_struct_0(k1_tex_2(X25,X26))
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,u1_struct_0(X25)) )
      & ( v7_struct_0(k1_tex_2(X25,X26))
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,u1_struct_0(X25)) )
      & ( v1_pre_topc(k1_tex_2(X25,X26))
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,u1_struct_0(X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ v7_struct_0(esk3_0)
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_40])]),c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_40])).

cnf(c_0_59,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ v7_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_27]),c_0_40])]),c_0_47])).

cnf(c_0_60,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ v7_struct_0(esk3_0)
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

fof(c_0_63,plain,(
    ! [X8] :
      ( v7_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_zfmisc_1(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).

cnf(c_0_64,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_27]),c_0_40])]),c_0_47])).

cnf(c_0_65,negated_conjecture,
    ( ~ v7_struct_0(esk3_0)
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_27]),c_0_40])]),c_0_47])).

cnf(c_0_66,plain,
    ( v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_43]),c_0_27]),c_0_40])]),c_0_47])).

cnf(c_0_68,negated_conjecture,
    ( ~ v7_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_43]),c_0_27]),c_0_40])]),c_0_47])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_58])]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:15:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.029 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 0.12/0.37  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.12/0.37  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 0.12/0.37  fof(cc1_zfmisc_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 0.12/0.37  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.12/0.37  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.12/0.37  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.12/0.37  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.12/0.37  fof(t8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~((v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))&v7_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 0.12/0.37  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.12/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.37  fof(cc10_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v7_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(~(v2_struct_0(X2))=>(~(v2_struct_0(X2))&~(v1_tex_2(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 0.12/0.37  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.12/0.37  fof(fc6_struct_0, axiom, ![X1]:((~(v7_struct_0(X1))&l1_struct_0(X1))=>~(v1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 0.12/0.37  fof(c_0_14, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.12/0.37  fof(c_0_15, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&((~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)))&(v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.12/0.37  fof(c_0_16, plain, ![X21, X22]:((~v1_subset_1(X22,X21)|X22!=X21|~m1_subset_1(X22,k1_zfmisc_1(X21)))&(X22=X21|v1_subset_1(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.12/0.37  fof(c_0_17, plain, ![X14, X16]:(((m1_subset_1(esk1_1(X14),X14)|~v1_zfmisc_1(X14)|v1_xboole_0(X14))&(X14=k6_domain_1(X14,esk1_1(X14))|~v1_zfmisc_1(X14)|v1_xboole_0(X14)))&(~m1_subset_1(X16,X14)|X14!=k6_domain_1(X14,X16)|v1_zfmisc_1(X14)|v1_xboole_0(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.12/0.37  fof(c_0_18, plain, ![X4]:(~v1_xboole_0(X4)|v1_zfmisc_1(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_20, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  fof(c_0_21, plain, ![X10, X11]:(v1_xboole_0(X10)|~m1_subset_1(X11,X10)|m1_subset_1(k6_domain_1(X10,X11),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.12/0.37  fof(c_0_22, plain, ![X17, X18, X19]:((~v1_tex_2(X18,X17)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|(X19!=u1_struct_0(X18)|v1_subset_1(X19,u1_struct_0(X17))))|~m1_pre_topc(X18,X17)|~l1_pre_topc(X17))&((m1_subset_1(esk2_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))|v1_tex_2(X18,X17)|~m1_pre_topc(X18,X17)|~l1_pre_topc(X17))&((esk2_2(X17,X18)=u1_struct_0(X18)|v1_tex_2(X18,X17)|~m1_pre_topc(X18,X17)|~l1_pre_topc(X17))&(~v1_subset_1(esk2_2(X17,X18),u1_struct_0(X17))|v1_tex_2(X18,X17)|~m1_pre_topc(X18,X17)|~l1_pre_topc(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.12/0.37  cnf(c_0_23, plain, (v1_zfmisc_1(X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)|X2!=k6_domain_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_24, plain, (v1_zfmisc_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),esk4_0)=u1_struct_0(esk3_0)|~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.37  cnf(c_0_26, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_28, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_29, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_30, plain, (v1_zfmisc_1(X1)|k6_domain_1(X1,X2)!=X1|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),esk4_0)=u1_struct_0(esk3_0)|v1_xboole_0(u1_struct_0(esk3_0))|~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.12/0.37  cnf(c_0_32, plain, (esk2_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_33, plain, (esk2_2(X1,X2)=u1_struct_0(X1)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_20]), c_0_29])).
% 0.12/0.37  fof(c_0_34, plain, ![X6, X7]:(~l1_pre_topc(X6)|(~m1_pre_topc(X7,X6)|l1_pre_topc(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.12/0.37  fof(c_0_35, plain, ![X23, X24]:(((~v2_struct_0(k1_tex_2(X23,X24))|(v2_struct_0(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,u1_struct_0(X23))))&(v1_pre_topc(k1_tex_2(X23,X24))|(v2_struct_0(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,u1_struct_0(X23)))))&(m1_pre_topc(k1_tex_2(X23,X24),X23)|(v2_struct_0(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,u1_struct_0(X23))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.12/0.37  fof(c_0_36, plain, ![X27, X28]:(v2_struct_0(X27)|~l1_struct_0(X27)|(~m1_subset_1(X28,u1_struct_0(X27))|(~v1_subset_1(k6_domain_1(u1_struct_0(X27),X28),u1_struct_0(X27))|~v7_struct_0(X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).
% 0.12/0.37  fof(c_0_37, plain, ![X9]:(~v7_struct_0(X9)|~l1_struct_0(X9)|v1_zfmisc_1(u1_struct_0(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_27])]), c_0_24])).
% 0.12/0.37  cnf(c_0_39, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  fof(c_0_41, plain, ![X5]:(~l1_pre_topc(X5)|l1_struct_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.37  cnf(c_0_42, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.37  cnf(c_0_43, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.37  fof(c_0_44, plain, ![X12, X13]:((~v2_struct_0(X13)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|(v2_struct_0(X12)|~v7_struct_0(X12)|~l1_pre_topc(X12)))&(~v1_tex_2(X13,X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|(v2_struct_0(X12)|~v7_struct_0(X12)|~l1_pre_topc(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).
% 0.12/0.37  cnf(c_0_45, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~v7_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_48, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,esk4_0))=u1_struct_0(esk3_0)|v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.12/0.37  cnf(c_0_50, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.37  cnf(c_0_51, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.37  cnf(c_0_52, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~v7_struct_0(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v7_struct_0(esk3_0)|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_27])]), c_0_47])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~v7_struct_0(k1_tex_2(esk3_0,esk4_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.12/0.37  cnf(c_0_55, plain, (v2_struct_0(X1)|l1_struct_0(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.12/0.37  fof(c_0_56, plain, ![X25, X26]:(((~v2_struct_0(k1_tex_2(X25,X26))|(v2_struct_0(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,u1_struct_0(X25))))&(v7_struct_0(k1_tex_2(X25,X26))|(v2_struct_0(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,u1_struct_0(X25)))))&(v1_pre_topc(k1_tex_2(X25,X26))|(v2_struct_0(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,u1_struct_0(X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (v2_struct_0(k1_tex_2(esk3_0,esk4_0))|~v7_struct_0(esk3_0)|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_40])]), c_0_47])).
% 0.12/0.37  cnf(c_0_58, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_40])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~v7_struct_0(k1_tex_2(esk3_0,esk4_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_27]), c_0_40])]), c_0_47])).
% 0.12/0.37  cnf(c_0_60, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.37  cnf(c_0_61, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (v2_struct_0(k1_tex_2(esk3_0,esk4_0))|~v7_struct_0(esk3_0)|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 0.12/0.37  fof(c_0_63, plain, ![X8]:(v7_struct_0(X8)|~l1_struct_0(X8)|~v1_zfmisc_1(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_27]), c_0_40])]), c_0_47])).
% 0.12/0.37  cnf(c_0_65, negated_conjecture, (~v7_struct_0(esk3_0)|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_27]), c_0_40])]), c_0_47])).
% 0.12/0.37  cnf(c_0_66, plain, (v7_struct_0(X1)|~l1_struct_0(X1)|~v1_zfmisc_1(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_43]), c_0_27]), c_0_40])]), c_0_47])).
% 0.12/0.37  cnf(c_0_68, negated_conjecture, (~v7_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_43]), c_0_27]), c_0_40])]), c_0_47])).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_58])]), c_0_68]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 70
% 0.12/0.37  # Proof object clause steps            : 41
% 0.12/0.37  # Proof object formula steps           : 29
% 0.12/0.37  # Proof object conjectures             : 23
% 0.12/0.37  # Proof object clause conjectures      : 20
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 21
% 0.12/0.37  # Proof object initial formulas used   : 14
% 0.12/0.37  # Proof object generating inferences   : 18
% 0.12/0.37  # Proof object simplifying inferences  : 40
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 14
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 29
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 28
% 0.12/0.37  # Processed clauses                    : 94
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 7
% 0.12/0.37  # ...remaining for further processing  : 87
% 0.12/0.37  # Other redundant clauses eliminated   : 2
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 6
% 0.12/0.37  # Backward-rewritten                   : 5
% 0.12/0.37  # Generated clauses                    : 83
% 0.12/0.37  # ...of the previous two non-trivial   : 77
% 0.12/0.37  # Contextual simplify-reflections      : 5
% 0.12/0.37  # Paramodulations                      : 81
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 2
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 48
% 0.12/0.37  #    Positive orientable unit clauses  : 4
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 2
% 0.12/0.37  #    Non-unit-clauses                  : 42
% 0.12/0.37  # Current number of unprocessed clauses: 36
% 0.12/0.37  # ...number of literals in the above   : 222
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 37
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 624
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 278
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 13
% 0.12/0.37  # Unit Clause-clause subsumption calls : 17
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 2
% 0.12/0.37  # BW rewrite match successes           : 2
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4335
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.035 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.038 s
% 0.12/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
