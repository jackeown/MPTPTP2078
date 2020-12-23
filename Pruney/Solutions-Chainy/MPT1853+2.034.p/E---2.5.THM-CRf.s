%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:30 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 426 expanded)
%              Number of clauses        :   53 ( 158 expanded)
%              Number of leaves         :   15 ( 106 expanded)
%              Depth                    :   19
%              Number of atoms          :  313 (1836 expanded)
%              Number of equality atoms :   16 (  32 expanded)
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

fof(l17_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

fof(t6_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(cc1_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( v1_subset_1(X2,X1)
           => v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).

fof(cc4_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ~ v1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

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

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(t7_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => v1_subset_1(k6_domain_1(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
              & v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

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
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | l1_struct_0(X15) ) ),
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
    ! [X20] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | ~ v1_xboole_0(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v1_tex_2(X26,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | X27 != u1_struct_0(X26)
        | v1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk2_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))
        | v1_tex_2(X26,X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) )
      & ( esk2_2(X25,X26) = u1_struct_0(X26)
        | v1_tex_2(X26,X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ v1_subset_1(esk2_2(X25,X26),u1_struct_0(X25))
        | v1_tex_2(X26,X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_22,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_pre_topc(X36,X35)
      | m1_subset_1(u1_struct_0(X36),k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l17_tex_2])])])).

fof(c_0_23,plain,(
    ! [X37,X38] :
      ( v1_xboole_0(X37)
      | ~ m1_subset_1(X38,X37)
      | ~ v1_subset_1(k6_domain_1(X37,X38),X37)
      | ~ v1_zfmisc_1(X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_27,plain,(
    ! [X23,X24] :
      ( v1_xboole_0(X23)
      | ~ v1_zfmisc_1(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | ~ v1_subset_1(X24,X23)
      | v1_xboole_0(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_tex_2])])])])).

fof(c_0_28,plain,(
    ! [X8,X9] :
      ( ~ v1_xboole_0(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | ~ v1_subset_1(X9,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).

cnf(c_0_29,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

fof(c_0_35,plain,(
    ! [X31,X32] :
      ( ( ~ v2_struct_0(k1_tex_2(X31,X32))
        | v2_struct_0(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) )
      & ( v1_pre_topc(k1_tex_2(X31,X32))
        | v2_struct_0(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) )
      & ( m1_pre_topc(k1_tex_2(X31,X32),X31)
        | v2_struct_0(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_zfmisc_1(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_34])).

fof(c_0_40,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X16)
      | l1_pre_topc(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X2)
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))
    | ~ v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_20])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_45,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_47,plain,(
    ! [X29,X30] :
      ( ( ~ v1_subset_1(X30,X29)
        | X30 != X29
        | ~ m1_subset_1(X30,k1_zfmisc_1(X29)) )
      & ( X30 = X29
        | v1_subset_1(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_48,plain,(
    ! [X39,X40] :
      ( v1_xboole_0(X39)
      | v1_zfmisc_1(X39)
      | ~ m1_subset_1(X40,X39)
      | v1_subset_1(k6_domain_1(X39,X40),X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).

fof(c_0_49,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X21)
      | ~ m1_subset_1(X22,X21)
      | k6_domain_1(X21,X22) = k1_tarski(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_25])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(esk3_0,esk4_0)))
    | ~ v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_54,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_20]),c_0_33])]),c_0_24])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_52])).

cnf(c_0_61,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_62,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X1)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_33])]),c_0_34])).

cnf(c_0_64,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | v1_subset_1(k1_tarski(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_58]),c_0_33])]),c_0_34])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_zfmisc_1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_20]),c_0_33])]),c_0_24])).

fof(c_0_66,plain,(
    ! [X41,X42] :
      ( v2_struct_0(X41)
      | ~ l1_struct_0(X41)
      | ~ m1_subset_1(X42,u1_struct_0(X41))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X41),X42),u1_struct_0(X41))
      | ~ v7_struct_0(X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(k1_tarski(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_58]),c_0_33])]),c_0_34])).

cnf(c_0_68,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_0))
    | v1_subset_1(k1_tarski(esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_zfmisc_1(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_46]),c_0_20]),c_0_33])]),c_0_24])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,esk4_0)) = u1_struct_0(esk3_0)
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ v1_subset_1(k1_tarski(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_20])])).

cnf(c_0_73,negated_conjecture,
    ( v1_subset_1(k1_tarski(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_57]),c_0_25])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,esk4_0)) = u1_struct_0(esk3_0)
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_76,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ v7_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ v7_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_33])).

fof(c_0_78,plain,(
    ! [X33,X34] :
      ( ( ~ v2_struct_0(k1_tex_2(X33,X34))
        | v2_struct_0(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_subset_1(X34,u1_struct_0(X33)) )
      & ( v7_struct_0(k1_tex_2(X33,X34))
        | v2_struct_0(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_subset_1(X34,u1_struct_0(X33)) )
      & ( v1_pre_topc(k1_tex_2(X33,X34))
        | v2_struct_0(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_subset_1(X34,u1_struct_0(X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_79,negated_conjecture,
    ( ~ v7_struct_0(k1_tex_2(esk3_0,esk4_0))
    | ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_77]),c_0_20]),c_0_33])]),c_0_24])).

cnf(c_0_80,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)
    | ~ l1_struct_0(k1_tex_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_20]),c_0_33])]),c_0_24])).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_60]),c_0_20]),c_0_33])]),c_0_24])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_46]),c_0_20]),c_0_33])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.20/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.029 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 0.20/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.40  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.40  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.20/0.40  fof(l17_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l17_tex_2)).
% 0.20/0.40  fof(t6_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.20/0.40  fof(cc1_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tex_2)).
% 0.20/0.40  fof(cc4_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~(v1_subset_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 0.20/0.40  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.20/0.40  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.40  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.20/0.40  fof(t7_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 0.20/0.40  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.20/0.40  fof(t8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~((v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))&v7_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 0.20/0.40  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.20/0.40  fof(c_0_15, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.20/0.40  fof(c_0_16, plain, ![X15]:(~l1_pre_topc(X15)|l1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.40  fof(c_0_17, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&((~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)))&(v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.40  fof(c_0_18, plain, ![X20]:(v2_struct_0(X20)|~l1_struct_0(X20)|~v1_xboole_0(u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.40  cnf(c_0_19, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  fof(c_0_21, plain, ![X25, X26, X27]:((~v1_tex_2(X26,X25)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|(X27!=u1_struct_0(X26)|v1_subset_1(X27,u1_struct_0(X25))))|~m1_pre_topc(X26,X25)|~l1_pre_topc(X25))&((m1_subset_1(esk2_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))|v1_tex_2(X26,X25)|~m1_pre_topc(X26,X25)|~l1_pre_topc(X25))&((esk2_2(X25,X26)=u1_struct_0(X26)|v1_tex_2(X26,X25)|~m1_pre_topc(X26,X25)|~l1_pre_topc(X25))&(~v1_subset_1(esk2_2(X25,X26),u1_struct_0(X25))|v1_tex_2(X26,X25)|~m1_pre_topc(X26,X25)|~l1_pre_topc(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.20/0.40  fof(c_0_22, plain, ![X35, X36]:(~l1_pre_topc(X35)|(~m1_pre_topc(X36,X35)|m1_subset_1(u1_struct_0(X36),k1_zfmisc_1(u1_struct_0(X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l17_tex_2])])])).
% 0.20/0.40  fof(c_0_23, plain, ![X37, X38]:(v1_xboole_0(X37)|(~m1_subset_1(X38,X37)|(~v1_subset_1(k6_domain_1(X37,X38),X37)|~v1_zfmisc_1(X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_25, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.40  fof(c_0_27, plain, ![X23, X24]:(v1_xboole_0(X23)|~v1_zfmisc_1(X23)|(~m1_subset_1(X24,k1_zfmisc_1(X23))|(~v1_subset_1(X24,X23)|v1_xboole_0(X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_tex_2])])])])).
% 0.20/0.40  fof(c_0_28, plain, ![X8, X9]:(~v1_xboole_0(X8)|(~m1_subset_1(X9,k1_zfmisc_1(X8))|~v1_subset_1(X9,X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).
% 0.20/0.40  cnf(c_0_29, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_30, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_31, plain, (v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~v1_subset_1(k6_domain_1(X1,X2),X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.20/0.40  fof(c_0_35, plain, ![X31, X32]:(((~v2_struct_0(k1_tex_2(X31,X32))|(v2_struct_0(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,u1_struct_0(X31))))&(v1_pre_topc(k1_tex_2(X31,X32))|(v2_struct_0(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,u1_struct_0(X31)))))&(m1_pre_topc(k1_tex_2(X31,X32),X31)|(v2_struct_0(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,u1_struct_0(X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.20/0.40  cnf(c_0_36, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_37, plain, (~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.40  cnf(c_0_38, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]), c_0_30])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_zfmisc_1(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])]), c_0_34])).
% 0.20/0.40  fof(c_0_40, plain, ![X16, X17]:(~l1_pre_topc(X16)|(~m1_pre_topc(X17,X16)|l1_pre_topc(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.40  cnf(c_0_41, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  cnf(c_0_42, plain, (v1_xboole_0(X1)|~v1_zfmisc_1(X2)|~v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (v1_subset_1(u1_struct_0(k1_tex_2(esk3_0,esk4_0)),u1_struct_0(esk3_0))|~v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_20])])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_pre_topc(X1,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.20/0.40  cnf(c_0_45, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.40  cnf(c_0_46, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  fof(c_0_47, plain, ![X29, X30]:((~v1_subset_1(X30,X29)|X30!=X29|~m1_subset_1(X30,k1_zfmisc_1(X29)))&(X30=X29|v1_subset_1(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.20/0.40  fof(c_0_48, plain, ![X39, X40]:(v1_xboole_0(X39)|v1_zfmisc_1(X39)|(~m1_subset_1(X40,X39)|v1_subset_1(k6_domain_1(X39,X40),X39))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).
% 0.20/0.40  fof(c_0_49, plain, ![X21, X22]:(v1_xboole_0(X21)|~m1_subset_1(X22,X21)|k6_domain_1(X21,X22)=k1_tarski(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.20/0.40  cnf(c_0_50, plain, (v2_struct_0(X1)|~l1_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2)))), inference(spm,[status(thm)],[c_0_41, c_0_25])).
% 0.20/0.40  cnf(c_0_51, negated_conjecture, (v1_xboole_0(u1_struct_0(k1_tex_2(esk3_0,esk4_0)))|~v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.20/0.40  cnf(c_0_52, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.40  cnf(c_0_53, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_54, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.40  cnf(c_0_55, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_57, plain, (v1_xboole_0(X1)|v1_zfmisc_1(X1)|v1_subset_1(k6_domain_1(X1,X2),X1)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.40  cnf(c_0_58, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (~v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_20]), c_0_33])]), c_0_24])).
% 0.20/0.40  cnf(c_0_60, plain, (v2_struct_0(X1)|l1_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_19, c_0_52])).
% 0.20/0.40  cnf(c_0_61, plain, (esk2_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_62, plain, (esk2_2(X1,X2)=u1_struct_0(X1)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_33])]), c_0_34])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|v1_subset_1(k1_tarski(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_58]), c_0_33])]), c_0_34])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (~v1_zfmisc_1(u1_struct_0(esk3_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_20]), c_0_33])]), c_0_24])).
% 0.20/0.40  fof(c_0_66, plain, ![X41, X42]:(v2_struct_0(X41)|~l1_struct_0(X41)|(~m1_subset_1(X42,u1_struct_0(X41))|(~v1_subset_1(k6_domain_1(u1_struct_0(X41),X42),u1_struct_0(X41))|~v7_struct_0(X41)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (~v1_tex_2(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(k1_tarski(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_58]), c_0_33])]), c_0_34])).
% 0.20/0.40  cnf(c_0_68, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_0))|v1_subset_1(k1_tarski(esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (~v1_zfmisc_1(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_46]), c_0_20]), c_0_33])]), c_0_24])).
% 0.20/0.40  cnf(c_0_71, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~v7_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.40  cnf(c_0_72, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,esk4_0))=u1_struct_0(esk3_0)|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~v1_subset_1(k1_tarski(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_20])])).
% 0.20/0.40  cnf(c_0_73, negated_conjecture, (v1_subset_1(k1_tarski(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.40  cnf(c_0_74, plain, (v1_zfmisc_1(u1_struct_0(X1))|v2_struct_0(X1)|~v7_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_57]), c_0_25])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,esk4_0))=u1_struct_0(esk3_0)|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])])).
% 0.20/0.40  cnf(c_0_76, negated_conjecture, (v2_struct_0(k1_tex_2(esk3_0,esk4_0))|~v7_struct_0(k1_tex_2(esk3_0,esk4_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_70])).
% 0.20/0.40  cnf(c_0_77, negated_conjecture, (v2_struct_0(k1_tex_2(esk3_0,esk4_0))|~v7_struct_0(k1_tex_2(esk3_0,esk4_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_76, c_0_33])).
% 0.20/0.40  fof(c_0_78, plain, ![X33, X34]:(((~v2_struct_0(k1_tex_2(X33,X34))|(v2_struct_0(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,u1_struct_0(X33))))&(v7_struct_0(k1_tex_2(X33,X34))|(v2_struct_0(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,u1_struct_0(X33)))))&(v1_pre_topc(k1_tex_2(X33,X34))|(v2_struct_0(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,u1_struct_0(X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.20/0.40  cnf(c_0_79, negated_conjecture, (~v7_struct_0(k1_tex_2(esk3_0,esk4_0))|~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_77]), c_0_20]), c_0_33])]), c_0_24])).
% 0.20/0.40  cnf(c_0_80, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.40  cnf(c_0_81, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)|~l1_struct_0(k1_tex_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_20]), c_0_33])]), c_0_24])).
% 0.20/0.40  cnf(c_0_82, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_60]), c_0_20]), c_0_33])]), c_0_24])).
% 0.20/0.40  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_46]), c_0_20]), c_0_33])]), c_0_24]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 84
% 0.20/0.40  # Proof object clause steps            : 53
% 0.20/0.40  # Proof object formula steps           : 31
% 0.20/0.40  # Proof object conjectures             : 30
% 0.20/0.40  # Proof object clause conjectures      : 27
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 23
% 0.20/0.40  # Proof object initial formulas used   : 15
% 0.20/0.40  # Proof object generating inferences   : 26
% 0.20/0.40  # Proof object simplifying inferences  : 56
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 20
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 36
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 36
% 0.20/0.40  # Processed clauses                    : 372
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 156
% 0.20/0.40  # ...remaining for further processing  : 216
% 0.20/0.40  # Other redundant clauses eliminated   : 2
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 23
% 0.20/0.40  # Backward-rewritten                   : 12
% 0.20/0.40  # Generated clauses                    : 631
% 0.20/0.40  # ...of the previous two non-trivial   : 556
% 0.20/0.40  # Contextual simplify-reflections      : 20
% 0.20/0.40  # Paramodulations                      : 627
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 2
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 143
% 0.20/0.40  #    Positive orientable unit clauses  : 12
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 7
% 0.20/0.40  #    Non-unit-clauses                  : 124
% 0.20/0.40  # Current number of unprocessed clauses: 225
% 0.20/0.40  # ...number of literals in the above   : 1233
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 71
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 2531
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 1187
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 121
% 0.20/0.40  # Unit Clause-clause subsumption calls : 144
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 10
% 0.20/0.40  # BW rewrite match successes           : 4
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 14464
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.051 s
% 0.20/0.40  # System time              : 0.007 s
% 0.20/0.40  # Total time               : 0.058 s
% 0.20/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
