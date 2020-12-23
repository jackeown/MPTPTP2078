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
% DateTime   : Thu Dec  3 11:19:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 204 expanded)
%              Number of clauses        :   39 (  73 expanded)
%              Number of leaves         :   12 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  262 ( 943 expanded)
%              Number of equality atoms :   11 (  17 expanded)
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

fof(t7_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => v1_subset_1(k6_domain_1(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

fof(cc1_zfmisc_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_zfmisc_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

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

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(t8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
              & v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(fc6_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_13,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X21)
      | v1_zfmisc_1(X21)
      | ~ m1_subset_1(X22,X21)
      | v1_subset_1(k6_domain_1(X21,X22),X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).

fof(c_0_14,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | v1_zfmisc_1(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).

fof(c_0_15,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v1_tex_2(X12,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | X13 != u1_struct_0(X12)
        | v1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_pre_topc(X12,X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk1_2(X11,X12),k1_zfmisc_1(u1_struct_0(X11)))
        | v1_tex_2(X12,X11)
        | ~ m1_pre_topc(X12,X11)
        | ~ l1_pre_topc(X11) )
      & ( esk1_2(X11,X12) = u1_struct_0(X12)
        | v1_tex_2(X12,X11)
        | ~ m1_pre_topc(X12,X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ v1_subset_1(esk1_2(X11,X12),u1_struct_0(X11))
        | v1_tex_2(X12,X11)
        | ~ m1_pre_topc(X12,X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ( ~ v1_subset_1(X16,X15)
        | X16 != X15
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) )
      & ( X16 = X15
        | v1_subset_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ( ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) )
    & ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_18,plain,
    ( v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ l1_struct_0(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X23),X24),u1_struct_0(X23))
      | ~ v7_struct_0(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v1_subset_1(k6_domain_1(X1,X2),X1)
    | v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X1)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_31,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,esk3_0)) = u1_struct_0(esk2_0)
    | v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

fof(c_0_35,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | l1_pre_topc(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_36,plain,(
    ! [X17,X18] :
      ( ( ~ v2_struct_0(k1_tex_2(X17,X18))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17)) )
      & ( v1_pre_topc(k1_tex_2(X17,X18))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17)) )
      & ( m1_pre_topc(k1_tex_2(X17,X18),X17)
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_37,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | l1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_38,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk2_0,esk3_0))
    | v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk2_0,esk3_0))
    | v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_46,plain,(
    ! [X9,X10] :
      ( ( ~ v2_struct_0(X10)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ v7_struct_0(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ v1_tex_2(X10,X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ v7_struct_0(X9)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).

cnf(c_0_47,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_26]),c_0_32])]),c_0_44])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_45])).

fof(c_0_51,plain,(
    ! [X19,X20] :
      ( ( ~ v2_struct_0(k1_tex_2(X19,X20))
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) )
      & ( v7_struct_0(k1_tex_2(X19,X20))
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) )
      & ( v1_pre_topc(k1_tex_2(X19,X20))
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v7_struct_0(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ v7_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_47]),c_0_26])]),c_0_44]),c_0_48])])).

cnf(c_0_54,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_26]),c_0_32])]),c_0_44])).

cnf(c_0_55,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ v7_struct_0(esk2_0)
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_32])]),c_0_44])).

fof(c_0_57,plain,(
    ! [X8] :
      ( v7_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_zfmisc_1(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).

cnf(c_0_58,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_26]),c_0_32])]),c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( ~ v7_struct_0(esk2_0)
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_56]),c_0_26]),c_0_32])]),c_0_44])).

cnf(c_0_60,plain,
    ( v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_40]),c_0_26]),c_0_32])]),c_0_44])).

cnf(c_0_62,negated_conjecture,
    ( ~ v7_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_40]),c_0_26]),c_0_32])]),c_0_44])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_48])]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:23:52 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 0.20/0.38  fof(t7_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 0.20/0.38  fof(cc1_zfmisc_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 0.20/0.38  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 0.20/0.38  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.20/0.38  fof(t8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~((v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))&v7_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 0.20/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.38  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.20/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.38  fof(cc10_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v7_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(~(v2_struct_0(X2))=>(~(v2_struct_0(X2))&~(v1_tex_2(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 0.20/0.38  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.20/0.38  fof(fc6_struct_0, axiom, ![X1]:((~(v7_struct_0(X1))&l1_struct_0(X1))=>~(v1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 0.20/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.20/0.38  fof(c_0_13, plain, ![X21, X22]:(v1_xboole_0(X21)|v1_zfmisc_1(X21)|(~m1_subset_1(X22,X21)|v1_subset_1(k6_domain_1(X21,X22),X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X4]:(~v1_xboole_0(X4)|v1_zfmisc_1(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).
% 0.20/0.38  fof(c_0_15, plain, ![X11, X12, X13]:((~v1_tex_2(X12,X11)|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))|(X13!=u1_struct_0(X12)|v1_subset_1(X13,u1_struct_0(X11))))|~m1_pre_topc(X12,X11)|~l1_pre_topc(X11))&((m1_subset_1(esk1_2(X11,X12),k1_zfmisc_1(u1_struct_0(X11)))|v1_tex_2(X12,X11)|~m1_pre_topc(X12,X11)|~l1_pre_topc(X11))&((esk1_2(X11,X12)=u1_struct_0(X12)|v1_tex_2(X12,X11)|~m1_pre_topc(X12,X11)|~l1_pre_topc(X11))&(~v1_subset_1(esk1_2(X11,X12),u1_struct_0(X11))|v1_tex_2(X12,X11)|~m1_pre_topc(X12,X11)|~l1_pre_topc(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.20/0.38  fof(c_0_16, plain, ![X15, X16]:((~v1_subset_1(X16,X15)|X16!=X15|~m1_subset_1(X16,k1_zfmisc_1(X15)))&(X16=X15|v1_subset_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.20/0.38  fof(c_0_17, negated_conjecture, ((~v2_struct_0(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&((~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)))&(v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.20/0.38  cnf(c_0_18, plain, (v1_xboole_0(X1)|v1_zfmisc_1(X1)|v1_subset_1(k6_domain_1(X1,X2),X1)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_19, plain, (v1_zfmisc_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_20, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_21, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_22, plain, (m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  fof(c_0_23, plain, ![X23, X24]:(v2_struct_0(X23)|~l1_struct_0(X23)|(~m1_subset_1(X24,u1_struct_0(X23))|(~v1_subset_1(k6_domain_1(u1_struct_0(X23),X24),u1_struct_0(X23))|~v7_struct_0(X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_25, plain, (v1_subset_1(k6_domain_1(X1,X2),X1)|v1_zfmisc_1(X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_27, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_28, plain, (esk1_2(X1,X2)=u1_struct_0(X1)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.20/0.38  cnf(c_0_29, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~v7_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.20/0.38  cnf(c_0_31, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_33, plain, (v2_struct_0(X1)|v1_zfmisc_1(u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,esk3_0))=u1_struct_0(esk2_0)|v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.20/0.38  fof(c_0_35, plain, ![X6, X7]:(~l1_pre_topc(X6)|(~m1_pre_topc(X7,X6)|l1_pre_topc(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.38  fof(c_0_36, plain, ![X17, X18]:(((~v2_struct_0(k1_tex_2(X17,X18))|(v2_struct_0(X17)|~l1_pre_topc(X17)|~m1_subset_1(X18,u1_struct_0(X17))))&(v1_pre_topc(k1_tex_2(X17,X18))|(v2_struct_0(X17)|~l1_pre_topc(X17)|~m1_subset_1(X18,u1_struct_0(X17)))))&(m1_pre_topc(k1_tex_2(X17,X18),X17)|(v2_struct_0(X17)|~l1_pre_topc(X17)|~m1_subset_1(X18,u1_struct_0(X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.20/0.38  fof(c_0_37, plain, ![X5]:(~l1_pre_topc(X5)|l1_struct_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (v2_struct_0(k1_tex_2(esk2_0,esk3_0))|v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~v7_struct_0(k1_tex_2(esk2_0,esk3_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.38  cnf(c_0_39, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_40, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_41, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.38  cnf(c_0_42, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (v2_struct_0(k1_tex_2(esk2_0,esk3_0))|v1_zfmisc_1(u1_struct_0(esk2_0))|~v7_struct_0(k1_tex_2(esk2_0,esk3_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_26])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_45, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.38  fof(c_0_46, plain, ![X9, X10]:((~v2_struct_0(X10)|v2_struct_0(X10)|~m1_pre_topc(X10,X9)|(v2_struct_0(X9)|~v7_struct_0(X9)|~l1_pre_topc(X9)))&(~v1_tex_2(X10,X9)|v2_struct_0(X10)|~m1_pre_topc(X10,X9)|(v2_struct_0(X9)|~v7_struct_0(X9)|~l1_pre_topc(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_32])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~v7_struct_0(k1_tex_2(esk2_0,esk3_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_26]), c_0_32])]), c_0_44])).
% 0.20/0.38  cnf(c_0_50, plain, (v2_struct_0(X1)|l1_struct_0(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_45])).
% 0.20/0.38  fof(c_0_51, plain, ![X19, X20]:(((~v2_struct_0(k1_tex_2(X19,X20))|(v2_struct_0(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,u1_struct_0(X19))))&(v7_struct_0(k1_tex_2(X19,X20))|(v2_struct_0(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,u1_struct_0(X19)))))&(v1_pre_topc(k1_tex_2(X19,X20))|(v2_struct_0(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,u1_struct_0(X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.20/0.38  cnf(c_0_52, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~v7_struct_0(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v7_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_47]), c_0_26])]), c_0_44]), c_0_48])])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~v7_struct_0(k1_tex_2(esk2_0,esk3_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_26]), c_0_32])]), c_0_44])).
% 0.20/0.38  cnf(c_0_55, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (v2_struct_0(k1_tex_2(esk2_0,esk3_0))|~v7_struct_0(esk2_0)|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_32])]), c_0_44])).
% 0.20/0.38  fof(c_0_57, plain, ![X8]:(v7_struct_0(X8)|~l1_struct_0(X8)|~v1_zfmisc_1(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_26]), c_0_32])]), c_0_44])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (~v7_struct_0(esk2_0)|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_56]), c_0_26]), c_0_32])]), c_0_44])).
% 0.20/0.38  cnf(c_0_60, plain, (v7_struct_0(X1)|~l1_struct_0(X1)|~v1_zfmisc_1(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_40]), c_0_26]), c_0_32])]), c_0_44])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (~v7_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_40]), c_0_26]), c_0_32])]), c_0_44])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_48])]), c_0_62]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 64
% 0.20/0.38  # Proof object clause steps            : 39
% 0.20/0.38  # Proof object formula steps           : 25
% 0.20/0.38  # Proof object conjectures             : 22
% 0.20/0.38  # Proof object clause conjectures      : 19
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 19
% 0.20/0.38  # Proof object initial formulas used   : 12
% 0.20/0.38  # Proof object generating inferences   : 19
% 0.20/0.38  # Proof object simplifying inferences  : 41
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 12
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 25
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 24
% 0.20/0.38  # Processed clauses                    : 78
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 5
% 0.20/0.38  # ...remaining for further processing  : 73
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 10
% 0.20/0.38  # Backward-rewritten                   : 3
% 0.20/0.38  # Generated clauses                    : 49
% 0.20/0.38  # ...of the previous two non-trivial   : 44
% 0.20/0.38  # Contextual simplify-reflections      : 2
% 0.20/0.38  # Paramodulations                      : 47
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 36
% 0.20/0.38  #    Positive orientable unit clauses  : 4
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 30
% 0.20/0.38  # Current number of unprocessed clauses: 12
% 0.20/0.38  # ...number of literals in the above   : 71
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 35
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 510
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 169
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 14
% 0.20/0.38  # Unit Clause-clause subsumption calls : 11
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3318
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.036 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
