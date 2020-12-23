%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:30 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 544 expanded)
%              Number of clauses        :   55 ( 200 expanded)
%              Number of leaves         :   16 ( 133 expanded)
%              Depth                    :   16
%              Number of atoms          :  295 (2385 expanded)
%              Number of equality atoms :   19 (  48 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => v1_subset_1(k6_domain_1(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

fof(cc2_realset1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_zfmisc_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_realset1)).

fof(t20_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v1_tex_2(k1_tex_2(X1,X2),X1)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

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

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t6_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(cc2_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_xboole_0(X2)
           => ~ v1_subset_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(t15_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ~ ( u1_struct_0(X2) = u1_struct_0(X1)
              & v1_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

fof(c_0_16,plain,(
    ! [X42,X43] :
      ( v1_xboole_0(X42)
      | v1_zfmisc_1(X42)
      | ~ m1_subset_1(X43,X42)
      | v1_subset_1(k6_domain_1(X42,X43),X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).

fof(c_0_17,plain,(
    ! [X23] :
      ( ~ v1_xboole_0(X23)
      | v1_zfmisc_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_realset1])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ( ~ v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) )
    & ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_22,plain,(
    ! [X32,X33] :
      ( ( ~ v2_struct_0(k1_tex_2(X32,X33))
        | v2_struct_0(X32)
        | ~ l1_pre_topc(X32)
        | ~ m1_subset_1(X33,u1_struct_0(X32)) )
      & ( v1_pre_topc(k1_tex_2(X32,X33))
        | v2_struct_0(X32)
        | ~ l1_pre_topc(X32)
        | ~ m1_subset_1(X33,u1_struct_0(X32)) )
      & ( m1_pre_topc(k1_tex_2(X32,X33),X32)
        | v2_struct_0(X32)
        | ~ l1_pre_topc(X32)
        | ~ m1_subset_1(X33,u1_struct_0(X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

cnf(c_0_23,plain,
    ( v1_subset_1(k6_domain_1(X1,X2),X1)
    | v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X26,X27,X28] :
      ( ( ~ v1_tex_2(X27,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | X28 != u1_struct_0(X27)
        | v1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk2_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v1_tex_2(X27,X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) )
      & ( esk2_2(X26,X27) = u1_struct_0(X27)
        | v1_tex_2(X27,X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ v1_subset_1(esk2_2(X26,X27),u1_struct_0(X26))
        | v1_tex_2(X27,X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

cnf(c_0_26,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X7,X8] :
      ( ~ v1_xboole_0(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_xboole_0(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_30,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | m1_subset_1(u1_struct_0(X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))
    | v1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_27])]),c_0_28])).

fof(c_0_35,plain,(
    ! [X34,X35] :
      ( ( ~ v2_struct_0(k1_tex_2(X34,X35))
        | v2_struct_0(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34)) )
      & ( v7_struct_0(k1_tex_2(X34,X35))
        | v2_struct_0(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34)) )
      & ( v1_pre_topc(k1_tex_2(X34,X35))
        | v2_struct_0(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

fof(c_0_36,plain,(
    ! [X30,X31] :
      ( ( ~ v1_subset_1(X31,X30)
        | X31 != X30
        | ~ m1_subset_1(X31,k1_zfmisc_1(X30)) )
      & ( X31 = X30
        | v1_subset_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,plain,(
    ! [X20] :
      ( ~ v7_struct_0(X20)
      | ~ l1_struct_0(X20)
      | v1_zfmisc_1(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_41,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk4_0))
    | ~ v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0))
    | v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_27])])).

cnf(c_0_43,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | l1_pre_topc(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_45,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | m1_subset_1(esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_27])])).

fof(c_0_47,plain,(
    ! [X19] :
      ( v2_struct_0(X19)
      | ~ l1_struct_0(X19)
      | ~ v1_xboole_0(u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_48,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_xboole_0(u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0))
    | v1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v7_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_24]),c_0_27])]),c_0_28])).

fof(c_0_52,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | l1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_53,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | v1_subset_1(esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_34]),c_0_27])])).

fof(c_0_58,plain,(
    ! [X40,X41] :
      ( v1_xboole_0(X40)
      | ~ m1_subset_1(X41,X40)
      | ~ v1_subset_1(k6_domain_1(X40,X41),X40)
      | ~ v1_zfmisc_1(X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).

cnf(c_0_59,negated_conjecture,
    ( v1_zfmisc_1(esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0)))
    | v1_zfmisc_1(u1_struct_0(esk4_0))
    | ~ l1_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_60,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( l1_pre_topc(k1_tex_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_34]),c_0_27])])).

cnf(c_0_62,negated_conjecture,
    ( esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_34]),c_0_27])])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ l1_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_66,negated_conjecture,
    ( v1_zfmisc_1(esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0)))
    | v1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_67,negated_conjecture,
    ( esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_62])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_60]),c_0_61])])).

fof(c_0_70,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X24)
      | ~ v1_zfmisc_1(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | v1_xboole_0(X25)
      | ~ v1_subset_1(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).

fof(c_0_71,plain,(
    ! [X38,X39] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_pre_topc(X39,X38)
      | u1_struct_0(X39) != u1_struct_0(X38)
      | ~ v1_tex_2(X39,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_tex_2])])])).

cnf(c_0_72,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_24])])).

cnf(c_0_73,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_27]),c_0_24])]),c_0_28])).

cnf(c_0_75,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_39])).

cnf(c_0_77,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | u1_struct_0(X2) != u1_struct_0(X1)
    | ~ v1_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])]),c_0_74])).

cnf(c_0_79,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X1,X2)
    | ~ v1_zfmisc_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[c_0_75,c_0_38])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_34]),c_0_27])])).

cnf(c_0_81,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) != u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_34]),c_0_27])])).

cnf(c_0_82,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_zfmisc_1(u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_39])).

cnf(c_0_83,negated_conjecture,
    ( v1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_73]),c_0_34]),c_0_27])])).

cnf(c_0_85,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ l1_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_60]),c_0_61])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_86]),c_0_27]),c_0_24])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:42:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.12/0.37  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.029 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t7_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 0.12/0.37  fof(cc2_realset1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_realset1)).
% 0.12/0.37  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 0.12/0.37  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.12/0.37  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 0.12/0.37  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.12/0.37  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.12/0.37  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.12/0.37  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.12/0.37  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.12/0.37  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.12/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.12/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.37  fof(t6_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 0.12/0.37  fof(cc2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_xboole_0(X2))=>~(v1_subset_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 0.12/0.37  fof(t15_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>~((u1_struct_0(X2)=u1_struct_0(X1)&v1_tex_2(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tex_2)).
% 0.12/0.37  fof(c_0_16, plain, ![X42, X43]:(v1_xboole_0(X42)|v1_zfmisc_1(X42)|(~m1_subset_1(X43,X42)|v1_subset_1(k6_domain_1(X42,X43),X42))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).
% 0.12/0.37  fof(c_0_17, plain, ![X23]:(~v1_xboole_0(X23)|v1_zfmisc_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_realset1])])).
% 0.12/0.37  fof(c_0_18, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.12/0.37  cnf(c_0_19, plain, (v1_xboole_0(X1)|v1_zfmisc_1(X1)|v1_subset_1(k6_domain_1(X1,X2),X1)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_20, plain, (v1_zfmisc_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_21, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&((~v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)))&(v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.12/0.37  fof(c_0_22, plain, ![X32, X33]:(((~v2_struct_0(k1_tex_2(X32,X33))|(v2_struct_0(X32)|~l1_pre_topc(X32)|~m1_subset_1(X33,u1_struct_0(X32))))&(v1_pre_topc(k1_tex_2(X32,X33))|(v2_struct_0(X32)|~l1_pre_topc(X32)|~m1_subset_1(X33,u1_struct_0(X32)))))&(m1_pre_topc(k1_tex_2(X32,X33),X32)|(v2_struct_0(X32)|~l1_pre_topc(X32)|~m1_subset_1(X33,u1_struct_0(X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.12/0.37  cnf(c_0_23, plain, (v1_subset_1(k6_domain_1(X1,X2),X1)|v1_zfmisc_1(X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  fof(c_0_25, plain, ![X26, X27, X28]:((~v1_tex_2(X27,X26)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(X28!=u1_struct_0(X27)|v1_subset_1(X28,u1_struct_0(X26))))|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))&((m1_subset_1(esk2_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))|v1_tex_2(X27,X26)|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))&((esk2_2(X26,X27)=u1_struct_0(X27)|v1_tex_2(X27,X26)|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))&(~v1_subset_1(esk2_2(X26,X27),u1_struct_0(X26))|v1_tex_2(X27,X26)|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.12/0.37  cnf(c_0_26, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  fof(c_0_29, plain, ![X7, X8]:(~v1_xboole_0(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.12/0.37  fof(c_0_30, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|m1_subset_1(u1_struct_0(X22),k1_zfmisc_1(u1_struct_0(X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (~v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))|v1_zfmisc_1(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.37  cnf(c_0_33, plain, (esk2_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (m1_pre_topc(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_24]), c_0_27])]), c_0_28])).
% 0.12/0.37  fof(c_0_35, plain, ![X34, X35]:(((~v2_struct_0(k1_tex_2(X34,X35))|(v2_struct_0(X34)|~l1_pre_topc(X34)|~m1_subset_1(X35,u1_struct_0(X34))))&(v7_struct_0(k1_tex_2(X34,X35))|(v2_struct_0(X34)|~l1_pre_topc(X34)|~m1_subset_1(X35,u1_struct_0(X34)))))&(v1_pre_topc(k1_tex_2(X34,X35))|(v2_struct_0(X34)|~l1_pre_topc(X34)|~m1_subset_1(X35,u1_struct_0(X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.12/0.37  fof(c_0_36, plain, ![X30, X31]:((~v1_subset_1(X31,X30)|X31!=X30|~m1_subset_1(X31,k1_zfmisc_1(X30)))&(X31=X30|v1_subset_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.12/0.37  cnf(c_0_37, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_38, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.37  cnf(c_0_39, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  fof(c_0_40, plain, ![X20]:(~v7_struct_0(X20)|~l1_struct_0(X20)|v1_zfmisc_1(u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk4_0))|~v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0))|v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_27])])).
% 0.12/0.37  cnf(c_0_43, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.37  fof(c_0_44, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|l1_pre_topc(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.12/0.37  cnf(c_0_45, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|m1_subset_1(esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_27])])).
% 0.12/0.37  fof(c_0_47, plain, ![X19]:(v2_struct_0(X19)|~l1_struct_0(X19)|~v1_xboole_0(u1_struct_0(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.12/0.37  cnf(c_0_48, plain, (v1_xboole_0(u1_struct_0(X1))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v1_xboole_0(u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.37  cnf(c_0_49, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0))|v1_zfmisc_1(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (v7_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_24]), c_0_27])]), c_0_28])).
% 0.12/0.37  fof(c_0_52, plain, ![X16]:(~l1_pre_topc(X16)|l1_struct_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.37  cnf(c_0_53, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.37  cnf(c_0_54, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_subset_1(esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.37  cnf(c_0_56, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_34]), c_0_27])])).
% 0.12/0.37  fof(c_0_58, plain, ![X40, X41]:(v1_xboole_0(X40)|(~m1_subset_1(X41,X40)|(~v1_subset_1(k6_domain_1(X40,X41),X40)|~v1_zfmisc_1(X40)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (v1_zfmisc_1(esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0)))|v1_zfmisc_1(u1_struct_0(esk4_0))|~l1_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.12/0.37  cnf(c_0_60, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.12/0.37  cnf(c_0_61, negated_conjecture, (l1_pre_topc(k1_tex_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_34]), c_0_27])])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_34]), c_0_27])])).
% 0.12/0.37  cnf(c_0_63, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))|~l1_struct_0(k1_tex_2(esk4_0,esk5_0))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.37  cnf(c_0_64, plain, (v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~v1_subset_1(k6_domain_1(X1,X2),X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.12/0.37  cnf(c_0_65, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_66, negated_conjecture, (v1_zfmisc_1(esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0)))|v1_zfmisc_1(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (esk2_2(esk4_0,k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_zfmisc_1(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_62])).
% 0.12/0.37  cnf(c_0_68, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_60]), c_0_61])])).
% 0.12/0.37  fof(c_0_70, plain, ![X24, X25]:(v1_xboole_0(X24)|~v1_zfmisc_1(X24)|(~m1_subset_1(X25,k1_zfmisc_1(X24))|(v1_xboole_0(X25)|~v1_subset_1(X25,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).
% 0.12/0.37  fof(c_0_71, plain, ![X38, X39]:(~l1_pre_topc(X38)|(~m1_pre_topc(X39,X38)|(u1_struct_0(X39)!=u1_struct_0(X38)|~v1_tex_2(X39,X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_tex_2])])])).
% 0.12/0.37  cnf(c_0_72, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))|~v1_zfmisc_1(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_24])])).
% 0.12/0.37  cnf(c_0_73, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.12/0.37  cnf(c_0_74, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_27]), c_0_24])]), c_0_28])).
% 0.12/0.37  cnf(c_0_75, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.12/0.37  cnf(c_0_76, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_45, c_0_39])).
% 0.12/0.37  cnf(c_0_77, plain, (~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|u1_struct_0(X2)!=u1_struct_0(X1)|~v1_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.12/0.37  cnf(c_0_78, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])]), c_0_74])).
% 0.12/0.37  cnf(c_0_79, plain, (v1_xboole_0(X1)|~v1_subset_1(X1,X2)|~v1_zfmisc_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[c_0_75, c_0_38])).
% 0.12/0.37  cnf(c_0_80, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_34]), c_0_27])])).
% 0.12/0.37  cnf(c_0_81, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))!=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_34]), c_0_27])])).
% 0.12/0.37  cnf(c_0_82, plain, (v1_xboole_0(u1_struct_0(X1))|~v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_zfmisc_1(u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_79, c_0_39])).
% 0.12/0.37  cnf(c_0_83, negated_conjecture, (v1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[c_0_80, c_0_81])).
% 0.12/0.37  cnf(c_0_84, negated_conjecture, (v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_73]), c_0_34]), c_0_27])])).
% 0.12/0.37  cnf(c_0_85, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))|~l1_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_56, c_0_84])).
% 0.12/0.37  cnf(c_0_86, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_60]), c_0_61])])).
% 0.12/0.37  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_86]), c_0_27]), c_0_24])]), c_0_28]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 88
% 0.12/0.37  # Proof object clause steps            : 55
% 0.12/0.37  # Proof object formula steps           : 33
% 0.12/0.37  # Proof object conjectures             : 35
% 0.12/0.37  # Proof object clause conjectures      : 32
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 23
% 0.12/0.37  # Proof object initial formulas used   : 16
% 0.12/0.37  # Proof object generating inferences   : 28
% 0.12/0.37  # Proof object simplifying inferences  : 50
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 21
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 38
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 37
% 0.12/0.37  # Processed clauses                    : 134
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 12
% 0.12/0.37  # ...remaining for further processing  : 121
% 0.12/0.37  # Other redundant clauses eliminated   : 2
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 9
% 0.12/0.37  # Backward-rewritten                   : 17
% 0.12/0.37  # Generated clauses                    : 88
% 0.12/0.37  # ...of the previous two non-trivial   : 83
% 0.12/0.37  # Contextual simplify-reflections      : 5
% 0.12/0.37  # Paramodulations                      : 85
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
% 0.12/0.37  # Current number of processed clauses  : 57
% 0.12/0.37  #    Positive orientable unit clauses  : 12
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 4
% 0.12/0.37  #    Non-unit-clauses                  : 41
% 0.12/0.37  # Current number of unprocessed clauses: 7
% 0.12/0.37  # ...number of literals in the above   : 25
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 63
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 879
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 467
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 13
% 0.12/0.37  # Unit Clause-clause subsumption calls : 39
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 4
% 0.12/0.37  # BW rewrite match successes           : 4
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4857
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.039 s
% 0.12/0.37  # System time              : 0.001 s
% 0.12/0.37  # Total time               : 0.040 s
% 0.12/0.37  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
