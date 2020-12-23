%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:29 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 269 expanded)
%              Number of clauses        :   35 (  93 expanded)
%              Number of leaves         :   12 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  270 (1252 expanded)
%              Number of equality atoms :    4 (   4 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(t9_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

fof(cc13_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & ~ v7_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & ~ v1_tex_2(X2,X1) )
           => ( ~ v2_struct_0(X2)
              & ~ v7_struct_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc13_tex_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(t8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
              & v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(cc6_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ~ v1_xboole_0(X2)
           => ( ~ v1_xboole_0(X2)
              & ~ v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tex_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ( ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) )
    & ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_14,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | v7_struct_0(X24)
      | ~ l1_struct_0(X24)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | v1_subset_1(k6_domain_1(u1_struct_0(X24),X25),u1_struct_0(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_tex_2])])])])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X10,X11] :
      ( ( ~ v2_struct_0(X11)
        | v2_struct_0(X11)
        | v1_tex_2(X11,X10)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X10)
        | v7_struct_0(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ v7_struct_0(X11)
        | v2_struct_0(X11)
        | v1_tex_2(X11,X10)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X10)
        | v7_struct_0(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc13_tex_2])])])])])).

fof(c_0_20,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | l1_struct_0(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_21,negated_conjecture,
    ( v7_struct_0(esk2_0)
    | ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | v1_tex_2(X1,X2)
    | v2_struct_0(X2)
    | v7_struct_0(X2)
    | ~ v7_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
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

cnf(c_0_26,negated_conjecture,
    ( v7_struct_0(esk2_0)
    | v2_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ v7_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])]),c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

fof(c_0_28,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ l1_struct_0(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X22),X23),u1_struct_0(X22))
      | ~ v7_struct_0(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v7_struct_0(esk2_0)
    | v2_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ v7_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

fof(c_0_31,plain,(
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

fof(c_0_32,plain,(
    ! [X5,X6] :
      ( ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X6,X5)
      | l1_pre_topc(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_33,plain,(
    ! [X14,X15,X16] :
      ( ( ~ v1_tex_2(X15,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | X16 != u1_struct_0(X15)
        | v1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk1_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))
        | v1_tex_2(X15,X14)
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X14) )
      & ( esk1_2(X14,X15) = u1_struct_0(X15)
        | v1_tex_2(X15,X14)
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ v1_subset_1(esk1_2(X14,X15),u1_struct_0(X14))
        | v1_tex_2(X15,X14)
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_34,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | m1_subset_1(u1_struct_0(X9),k1_zfmisc_1(u1_struct_0(X8))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( v7_struct_0(esk2_0)
    | ~ v7_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_17]),c_0_23])]),c_0_18])).

cnf(c_0_38,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_41,plain,(
    ! [X12,X13] :
      ( ( ~ v1_xboole_0(X13)
        | v1_xboole_0(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v7_struct_0(X12)
        | ~ l1_struct_0(X12) )
      & ( ~ v1_subset_1(X13,u1_struct_0(X12))
        | v1_xboole_0(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v7_struct_0(X12)
        | ~ l1_struct_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tex_2])])])])])).

cnf(c_0_42,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ v7_struct_0(esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_17])]),c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( v7_struct_0(esk2_0)
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_17]),c_0_23])]),c_0_18])).

fof(c_0_46,plain,(
    ! [X7] :
      ( v2_struct_0(X7)
      | ~ l1_struct_0(X7)
      | ~ v1_xboole_0(u1_struct_0(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v7_struct_0(X2)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_42]),c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ v7_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_27])])).

cnf(c_0_51,negated_conjecture,
    ( v7_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_17]),c_0_23])]),c_0_18])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_47])).

cnf(c_0_54,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X2)
    | ~ v1_tex_2(X1,X2)
    | ~ v7_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_24]),c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_52]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(esk2_0,esk3_0)))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_51]),c_0_23])]),c_0_18])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_17]),c_0_23])]),c_0_18])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_40]),c_0_17]),c_0_23])]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.19/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.051 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 0.19/0.40  fof(t9_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&~(v7_struct_0(X1)))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tex_2)).
% 0.19/0.40  fof(cc13_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&~(v7_struct_0(X1)))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((~(v2_struct_0(X2))&~(v1_tex_2(X2,X1)))=>(~(v2_struct_0(X2))&~(v7_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc13_tex_2)).
% 0.19/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.40  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.19/0.40  fof(t8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~((v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))&v7_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 0.19/0.40  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.19/0.40  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.40  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 0.19/0.40  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.40  fof(cc6_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v7_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~(v1_xboole_0(X2))=>(~(v1_xboole_0(X2))&~(v1_subset_1(X2,u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tex_2)).
% 0.19/0.40  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.40  fof(c_0_12, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.19/0.40  fof(c_0_13, negated_conjecture, ((~v2_struct_0(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&((~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)))&(v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.19/0.40  fof(c_0_14, plain, ![X24, X25]:(v2_struct_0(X24)|v7_struct_0(X24)|~l1_struct_0(X24)|(~m1_subset_1(X25,u1_struct_0(X24))|v1_subset_1(k6_domain_1(u1_struct_0(X24),X25),u1_struct_0(X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_tex_2])])])])).
% 0.19/0.40  cnf(c_0_15, negated_conjecture, (~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_16, plain, (v2_struct_0(X1)|v7_struct_0(X1)|v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  fof(c_0_19, plain, ![X10, X11]:((~v2_struct_0(X11)|(v2_struct_0(X11)|v1_tex_2(X11,X10))|~m1_pre_topc(X11,X10)|(v2_struct_0(X10)|v7_struct_0(X10)|~l1_pre_topc(X10)))&(~v7_struct_0(X11)|(v2_struct_0(X11)|v1_tex_2(X11,X10))|~m1_pre_topc(X11,X10)|(v2_struct_0(X10)|v7_struct_0(X10)|~l1_pre_topc(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc13_tex_2])])])])])).
% 0.19/0.40  fof(c_0_20, plain, ![X4]:(~l1_pre_topc(X4)|l1_struct_0(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.40  cnf(c_0_21, negated_conjecture, (v7_struct_0(esk2_0)|~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])]), c_0_18])).
% 0.19/0.40  cnf(c_0_22, plain, (v2_struct_0(X1)|v1_tex_2(X1,X2)|v2_struct_0(X2)|v7_struct_0(X2)|~v7_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_24, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  fof(c_0_25, plain, ![X18, X19]:(((~v2_struct_0(k1_tex_2(X18,X19))|(v2_struct_0(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,u1_struct_0(X18))))&(v1_pre_topc(k1_tex_2(X18,X19))|(v2_struct_0(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,u1_struct_0(X18)))))&(m1_pre_topc(k1_tex_2(X18,X19),X18)|(v2_struct_0(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,u1_struct_0(X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (v7_struct_0(esk2_0)|v2_struct_0(k1_tex_2(esk2_0,esk3_0))|~v7_struct_0(k1_tex_2(esk2_0,esk3_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])]), c_0_18])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 0.19/0.40  fof(c_0_28, plain, ![X22, X23]:(v2_struct_0(X22)|~l1_struct_0(X22)|(~m1_subset_1(X23,u1_struct_0(X22))|(~v1_subset_1(k6_domain_1(u1_struct_0(X22),X23),u1_struct_0(X22))|~v7_struct_0(X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).
% 0.19/0.40  cnf(c_0_29, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (v7_struct_0(esk2_0)|v2_struct_0(k1_tex_2(esk2_0,esk3_0))|~v7_struct_0(k1_tex_2(esk2_0,esk3_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27])])).
% 0.19/0.40  fof(c_0_31, plain, ![X20, X21]:(((~v2_struct_0(k1_tex_2(X20,X21))|(v2_struct_0(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20))))&(v7_struct_0(k1_tex_2(X20,X21))|(v2_struct_0(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20)))))&(v1_pre_topc(k1_tex_2(X20,X21))|(v2_struct_0(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.19/0.40  fof(c_0_32, plain, ![X5, X6]:(~l1_pre_topc(X5)|(~m1_pre_topc(X6,X5)|l1_pre_topc(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.40  fof(c_0_33, plain, ![X14, X15, X16]:((~v1_tex_2(X15,X14)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(X16!=u1_struct_0(X15)|v1_subset_1(X16,u1_struct_0(X14))))|~m1_pre_topc(X15,X14)|~l1_pre_topc(X14))&((m1_subset_1(esk1_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))|v1_tex_2(X15,X14)|~m1_pre_topc(X15,X14)|~l1_pre_topc(X14))&((esk1_2(X14,X15)=u1_struct_0(X15)|v1_tex_2(X15,X14)|~m1_pre_topc(X15,X14)|~l1_pre_topc(X14))&(~v1_subset_1(esk1_2(X14,X15),u1_struct_0(X14))|v1_tex_2(X15,X14)|~m1_pre_topc(X15,X14)|~l1_pre_topc(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.19/0.40  fof(c_0_34, plain, ![X8, X9]:(~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|m1_subset_1(u1_struct_0(X9),k1_zfmisc_1(u1_struct_0(X8))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.40  cnf(c_0_35, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~v7_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (v7_struct_0(esk2_0)|~v7_struct_0(k1_tex_2(esk2_0,esk3_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_17]), c_0_23])]), c_0_18])).
% 0.19/0.40  cnf(c_0_38, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_39, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  cnf(c_0_40, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  fof(c_0_41, plain, ![X12, X13]:((~v1_xboole_0(X13)|v1_xboole_0(X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v7_struct_0(X12)|~l1_struct_0(X12)))&(~v1_subset_1(X13,u1_struct_0(X12))|v1_xboole_0(X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v7_struct_0(X12)|~l1_struct_0(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tex_2])])])])])).
% 0.19/0.40  cnf(c_0_42, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_43, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v7_struct_0(esk2_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_17])]), c_0_18])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (v7_struct_0(esk2_0)|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_17]), c_0_23])]), c_0_18])).
% 0.19/0.40  fof(c_0_46, plain, ![X7]:(v2_struct_0(X7)|~l1_struct_0(X7)|~v1_xboole_0(u1_struct_0(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.40  cnf(c_0_47, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.40  cnf(c_0_48, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|~v1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v7_struct_0(X2)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.40  cnf(c_0_49, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_42]), c_0_43])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v7_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_27])])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (v7_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_17]), c_0_23])]), c_0_18])).
% 0.19/0.40  cnf(c_0_52, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.40  cnf(c_0_53, plain, (v2_struct_0(X1)|l1_struct_0(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_24, c_0_47])).
% 0.19/0.40  cnf(c_0_54, plain, (v1_xboole_0(u1_struct_0(X1))|v2_struct_0(X2)|~v1_tex_2(X1,X2)|~v7_struct_0(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_24]), c_0_43])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 0.19/0.40  cnf(c_0_56, plain, (v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_52]), c_0_53])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (v1_xboole_0(u1_struct_0(k1_tex_2(esk2_0,esk3_0)))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_51]), c_0_23])]), c_0_18])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_17]), c_0_23])]), c_0_18])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_40]), c_0_17]), c_0_23])]), c_0_18]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 60
% 0.19/0.40  # Proof object clause steps            : 35
% 0.19/0.40  # Proof object formula steps           : 25
% 0.19/0.40  # Proof object conjectures             : 21
% 0.19/0.40  # Proof object clause conjectures      : 18
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 17
% 0.19/0.40  # Proof object initial formulas used   : 12
% 0.19/0.40  # Proof object generating inferences   : 14
% 0.19/0.40  # Proof object simplifying inferences  : 44
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 12
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 25
% 0.19/0.40  # Removed in clause preprocessing      : 2
% 0.19/0.40  # Initial clauses in saturation        : 23
% 0.19/0.40  # Processed clauses                    : 67
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 3
% 0.19/0.40  # ...remaining for further processing  : 64
% 0.19/0.40  # Other redundant clauses eliminated   : 1
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 2
% 0.19/0.40  # Backward-rewritten                   : 9
% 0.19/0.40  # Generated clauses                    : 29
% 0.19/0.40  # ...of the previous two non-trivial   : 26
% 0.19/0.40  # Contextual simplify-reflections      : 4
% 0.19/0.40  # Paramodulations                      : 28
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 1
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 31
% 0.19/0.40  #    Positive orientable unit clauses  : 5
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 4
% 0.19/0.40  #    Non-unit-clauses                  : 22
% 0.19/0.40  # Current number of unprocessed clauses: 0
% 0.19/0.40  # ...number of literals in the above   : 0
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 32
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 249
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 91
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 9
% 0.19/0.40  # Unit Clause-clause subsumption calls : 4
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 3
% 0.19/0.40  # BW rewrite match successes           : 3
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 3137
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.054 s
% 0.19/0.40  # System time              : 0.008 s
% 0.19/0.40  # Total time               : 0.061 s
% 0.19/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
