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
% DateTime   : Thu Dec  3 11:19:28 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 241 expanded)
%              Number of clauses        :   41 (  88 expanded)
%              Number of leaves         :   13 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  267 (1055 expanded)
%              Number of equality atoms :   10 (  20 expanded)
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

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t7_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => v1_subset_1(k6_domain_1(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

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

fof(t6_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

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

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_14,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | l1_struct_0(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ( ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) )
    & ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X7] :
      ( v2_struct_0(X7)
      | ~ l1_struct_0(X7)
      | ~ v1_xboole_0(u1_struct_0(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_17,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X24)
      | v1_zfmisc_1(X24)
      | ~ m1_subset_1(X25,X24)
      | v1_subset_1(k6_domain_1(X24,X25),X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v1_tex_2(X13,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != u1_struct_0(X13)
        | v1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk1_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | v1_tex_2(X13,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) )
      & ( esk1_2(X12,X13) = u1_struct_0(X13)
        | v1_tex_2(X13,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ v1_subset_1(esk1_2(X12,X13),u1_struct_0(X12))
        | v1_tex_2(X13,X12)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_28,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_31,plain,
    ( v1_tex_2(X1,X2)
    | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_32,plain,(
    ! [X16,X17] :
      ( ( ~ v1_subset_1(X17,X16)
        | X17 != X16
        | ~ m1_subset_1(X17,k1_zfmisc_1(X16)) )
      & ( X17 = X16
        | v1_subset_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_18])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_29])).

fof(c_0_37,plain,(
    ! [X22,X23] :
      ( v1_xboole_0(X22)
      | ~ m1_subset_1(X23,X22)
      | ~ v1_subset_1(k6_domain_1(X22,X23),X22)
      | ~ v1_zfmisc_1(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).

fof(c_0_38,plain,(
    ! [X9] :
      ( ~ v7_struct_0(X9)
      | ~ l1_struct_0(X9)
      | v1_zfmisc_1(u1_struct_0(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,esk3_0)) = u1_struct_0(esk2_0)
    | v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_36]),c_0_18])])).

fof(c_0_41,plain,(
    ! [X5,X6] :
      ( ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X6,X5)
      | l1_pre_topc(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_42,plain,(
    ! [X18,X19] :
      ( ( ~ v2_struct_0(k1_tex_2(X18,X19))
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18)) )
      & ( v1_pre_topc(k1_tex_2(X18,X19))
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18)) )
      & ( m1_pre_topc(k1_tex_2(X18,X19),X18)
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_43,plain,(
    ! [X10,X11] :
      ( ( ~ v2_struct_0(X11)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X10)
        | ~ v7_struct_0(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ v1_tex_2(X11,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X10)
        | ~ v7_struct_0(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,esk3_0)) = u1_struct_0(esk2_0)
    | v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_48,plain,(
    ! [X20,X21] :
      ( ( ~ v2_struct_0(k1_tex_2(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) )
      & ( v7_struct_0(k1_tex_2(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) )
      & ( v1_pre_topc(k1_tex_2(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_49,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v7_struct_0(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ v1_zfmisc_1(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_26])]),c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v7_struct_0(esk2_0)
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_18])]),c_0_20])).

cnf(c_0_58,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_26]),c_0_18])]),c_0_20])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v7_struct_0(esk2_0)
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_26]),c_0_18])]),c_0_20])).

fof(c_0_61,plain,(
    ! [X8] :
      ( v7_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_zfmisc_1(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).

cnf(c_0_62,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_26]),c_0_18])]),c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v7_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_50]),c_0_26]),c_0_18])]),c_0_20])).

cnf(c_0_64,plain,
    ( v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_50]),c_0_26]),c_0_18])]),c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( ~ v7_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_46]),c_0_22])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_22])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:17:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  # Version: 2.5pre002
% 0.13/0.36  # No SInE strategy applied
% 0.13/0.36  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.029 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 0.13/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.39  fof(t7_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 0.13/0.39  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.13/0.39  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.13/0.39  fof(t6_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.13/0.39  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.13/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.39  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.13/0.39  fof(cc10_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v7_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(~(v2_struct_0(X2))=>(~(v2_struct_0(X2))&~(v1_tex_2(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 0.13/0.39  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.13/0.39  fof(fc6_struct_0, axiom, ![X1]:((~(v7_struct_0(X1))&l1_struct_0(X1))=>~(v1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 0.13/0.39  fof(c_0_13, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.13/0.39  fof(c_0_14, plain, ![X4]:(~l1_pre_topc(X4)|l1_struct_0(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.39  fof(c_0_15, negated_conjecture, ((~v2_struct_0(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&((~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)))&(v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.13/0.39  fof(c_0_16, plain, ![X7]:(v2_struct_0(X7)|~l1_struct_0(X7)|~v1_xboole_0(u1_struct_0(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.39  cnf(c_0_17, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  fof(c_0_19, plain, ![X24, X25]:(v1_xboole_0(X24)|v1_zfmisc_1(X24)|(~m1_subset_1(X25,X24)|v1_subset_1(k6_domain_1(X24,X25),X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).
% 0.13/0.39  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_21, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.39  fof(c_0_23, plain, ![X12, X13, X14]:((~v1_tex_2(X13,X12)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(X14!=u1_struct_0(X13)|v1_subset_1(X14,u1_struct_0(X12))))|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))&((m1_subset_1(esk1_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|v1_tex_2(X13,X12)|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))&((esk1_2(X12,X13)=u1_struct_0(X13)|v1_tex_2(X13,X12)|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))&(~v1_subset_1(esk1_2(X12,X13),u1_struct_0(X12))|v1_tex_2(X13,X12)|~m1_pre_topc(X13,X12)|~l1_pre_topc(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_25, plain, (v1_xboole_0(X1)|v1_zfmisc_1(X1)|v1_subset_1(k6_domain_1(X1,X2),X1)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.13/0.39  cnf(c_0_28, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_29, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])]), c_0_27])).
% 0.13/0.39  cnf(c_0_31, plain, (v1_tex_2(X1,X2)|~v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.39  fof(c_0_32, plain, ![X16, X17]:((~v1_subset_1(X17,X16)|X17!=X16|~m1_subset_1(X17,k1_zfmisc_1(X16)))&(X17=X16|v1_subset_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.13/0.39  cnf(c_0_33, plain, (m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~v1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_18])])).
% 0.13/0.39  cnf(c_0_35, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_36, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))|v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_33, c_0_29])).
% 0.13/0.39  fof(c_0_37, plain, ![X22, X23]:(v1_xboole_0(X22)|(~m1_subset_1(X23,X22)|(~v1_subset_1(k6_domain_1(X22,X23),X22)|~v1_zfmisc_1(X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).
% 0.13/0.39  fof(c_0_38, plain, ![X9]:(~v7_struct_0(X9)|~l1_struct_0(X9)|v1_zfmisc_1(u1_struct_0(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,esk3_0))=u1_struct_0(esk2_0)|v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (m1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))|v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_36]), c_0_18])])).
% 0.13/0.39  fof(c_0_41, plain, ![X5, X6]:(~l1_pre_topc(X5)|(~m1_pre_topc(X6,X5)|l1_pre_topc(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.39  fof(c_0_42, plain, ![X18, X19]:(((~v2_struct_0(k1_tex_2(X18,X19))|(v2_struct_0(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,u1_struct_0(X18))))&(v1_pre_topc(k1_tex_2(X18,X19))|(v2_struct_0(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,u1_struct_0(X18)))))&(m1_pre_topc(k1_tex_2(X18,X19),X18)|(v2_struct_0(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,u1_struct_0(X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.13/0.39  fof(c_0_43, plain, ![X10, X11]:((~v2_struct_0(X11)|v2_struct_0(X11)|~m1_pre_topc(X11,X10)|(v2_struct_0(X10)|~v7_struct_0(X10)|~l1_pre_topc(X10)))&(~v1_tex_2(X11,X10)|v2_struct_0(X11)|~m1_pre_topc(X11,X10)|(v2_struct_0(X10)|~v7_struct_0(X10)|~l1_pre_topc(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).
% 0.13/0.39  cnf(c_0_44, plain, (v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~v1_subset_1(k6_domain_1(X1,X2),X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_46, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,esk3_0))=u1_struct_0(esk2_0)|v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.39  fof(c_0_48, plain, ![X20, X21]:(((~v2_struct_0(k1_tex_2(X20,X21))|(v2_struct_0(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20))))&(v7_struct_0(k1_tex_2(X20,X21))|(v2_struct_0(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20)))))&(v1_pre_topc(k1_tex_2(X20,X21))|(v2_struct_0(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.13/0.39  cnf(c_0_49, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.39  cnf(c_0_50, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.39  cnf(c_0_51, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~v7_struct_0(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v1_zfmisc_1(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_26])]), c_0_27])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~v7_struct_0(k1_tex_2(esk2_0,esk3_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.39  cnf(c_0_54, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.39  cnf(c_0_55, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.39  cnf(c_0_56, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (v2_struct_0(k1_tex_2(esk2_0,esk3_0))|~v1_zfmisc_1(u1_struct_0(esk2_0))|~v7_struct_0(esk2_0)|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_18])]), c_0_20])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_26]), c_0_18])]), c_0_20])).
% 0.13/0.39  cnf(c_0_59, plain, (v2_struct_0(X1)|l1_struct_0(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_17, c_0_55])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (~v1_zfmisc_1(u1_struct_0(esk2_0))|~v7_struct_0(esk2_0)|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_26]), c_0_18])]), c_0_20])).
% 0.13/0.39  fof(c_0_61, plain, ![X8]:(v7_struct_0(X8)|~l1_struct_0(X8)|~v1_zfmisc_1(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_26]), c_0_18])]), c_0_20])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (~v1_zfmisc_1(u1_struct_0(esk2_0))|~v7_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_50]), c_0_26]), c_0_18])]), c_0_20])).
% 0.13/0.39  cnf(c_0_64, plain, (v7_struct_0(X1)|~l1_struct_0(X1)|~v1_zfmisc_1(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_50]), c_0_26]), c_0_18])]), c_0_20])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (~v7_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_46]), c_0_22])])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_22])]), c_0_66]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 68
% 0.13/0.39  # Proof object clause steps            : 41
% 0.13/0.39  # Proof object formula steps           : 27
% 0.13/0.39  # Proof object conjectures             : 25
% 0.13/0.39  # Proof object clause conjectures      : 22
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 20
% 0.13/0.39  # Proof object initial formulas used   : 13
% 0.13/0.39  # Proof object generating inferences   : 21
% 0.13/0.39  # Proof object simplifying inferences  : 40
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 13
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 26
% 0.13/0.39  # Removed in clause preprocessing      : 1
% 0.13/0.39  # Initial clauses in saturation        : 25
% 0.13/0.39  # Processed clauses                    : 85
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 5
% 0.13/0.39  # ...remaining for further processing  : 80
% 0.13/0.39  # Other redundant clauses eliminated   : 2
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 10
% 0.13/0.39  # Backward-rewritten                   : 7
% 0.13/0.39  # Generated clauses                    : 59
% 0.13/0.39  # ...of the previous two non-trivial   : 52
% 0.13/0.39  # Contextual simplify-reflections      : 1
% 0.13/0.39  # Paramodulations                      : 57
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
% 0.13/0.39  # Current number of processed clauses  : 38
% 0.13/0.39  #    Positive orientable unit clauses  : 4
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 3
% 0.13/0.39  #    Non-unit-clauses                  : 31
% 0.13/0.39  # Current number of unprocessed clauses: 12
% 0.13/0.39  # ...number of literals in the above   : 72
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 40
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 383
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 168
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 15
% 0.13/0.39  # Unit Clause-clause subsumption calls : 11
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 1
% 0.13/0.39  # BW rewrite match successes           : 1
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 3543
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.033 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.037 s
% 0.13/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
