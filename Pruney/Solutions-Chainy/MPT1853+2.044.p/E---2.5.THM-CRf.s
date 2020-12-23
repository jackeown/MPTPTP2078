%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:31 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  116 (1842 expanded)
%              Number of clauses        :   75 ( 674 expanded)
%              Number of leaves         :   20 ( 455 expanded)
%              Depth                    :   26
%              Number of atoms          :  382 (8175 expanded)
%              Number of equality atoms :   53 ( 294 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

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

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(fc6_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_21,plain,(
    ! [X40,X41] :
      ( ( ~ v2_struct_0(k1_tex_2(X40,X41))
        | v2_struct_0(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) )
      & ( v1_pre_topc(k1_tex_2(X40,X41))
        | v2_struct_0(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) )
      & ( m1_pre_topc(k1_tex_2(X40,X41),X40)
        | v2_struct_0(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ( ~ v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) )
    & ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_23,plain,(
    ! [X23,X24] :
      ( v1_xboole_0(X23)
      | ~ m1_subset_1(X24,X23)
      | m1_subset_1(k6_domain_1(X23,X24),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_24,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v1_tex_2(X35,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | X36 != u1_struct_0(X35)
        | v1_subset_1(X36,u1_struct_0(X34))
        | ~ m1_pre_topc(X35,X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk3_2(X34,X35),k1_zfmisc_1(u1_struct_0(X34)))
        | v1_tex_2(X35,X34)
        | ~ m1_pre_topc(X35,X34)
        | ~ l1_pre_topc(X34) )
      & ( esk3_2(X34,X35) = u1_struct_0(X35)
        | v1_tex_2(X35,X34)
        | ~ m1_pre_topc(X35,X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ v1_subset_1(esk3_2(X34,X35),u1_struct_0(X34))
        | v1_tex_2(X35,X34)
        | ~ m1_pre_topc(X35,X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

cnf(c_0_25,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X38,X39] :
      ( ( ~ v1_subset_1(X39,X38)
        | X39 != X38
        | ~ m1_subset_1(X39,k1_zfmisc_1(X38)) )
      & ( X39 = X38
        | v1_subset_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_33,plain,
    ( esk3_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | m1_subset_1(esk3_2(esk4_0,k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_27])])).

cnf(c_0_37,negated_conjecture,
    ( esk3_2(esk4_0,k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(k1_tex_2(esk4_0,esk5_0))
    | v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_32]),c_0_27])])).

cnf(c_0_38,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = u1_struct_0(esk4_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | m1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_32]),c_0_27])])).

fof(c_0_43,plain,(
    ! [X42,X43] :
      ( ( ~ v2_struct_0(k1_tex_2(X42,X43))
        | v2_struct_0(X42)
        | ~ l1_pre_topc(X42)
        | ~ m1_subset_1(X43,u1_struct_0(X42)) )
      & ( v7_struct_0(k1_tex_2(X42,X43))
        | v2_struct_0(X42)
        | ~ l1_pre_topc(X42)
        | ~ m1_subset_1(X43,u1_struct_0(X42)) )
      & ( v1_pre_topc(k1_tex_2(X42,X43))
        | v2_struct_0(X42)
        | ~ l1_pre_topc(X42)
        | ~ m1_subset_1(X43,u1_struct_0(X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

fof(c_0_44,plain,(
    ! [X22] :
      ( ~ v7_struct_0(X22)
      | ~ l1_struct_0(X22)
      | v1_zfmisc_1(u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_45,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = u1_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_41]),c_0_42])).

cnf(c_0_47,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_48,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | l1_pre_topc(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_49,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | k6_domain_1(u1_struct_0(esk4_0),esk5_0) = u1_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( v7_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_26]),c_0_27])]),c_0_28])).

fof(c_0_52,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_53,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_54,plain,(
    ! [X31,X33] :
      ( ( m1_subset_1(esk2_1(X31),X31)
        | ~ v1_zfmisc_1(X31)
        | v1_xboole_0(X31) )
      & ( X31 = k6_domain_1(X31,esk2_1(X31))
        | ~ v1_zfmisc_1(X31)
        | v1_xboole_0(X31) )
      & ( ~ m1_subset_1(X33,X31)
        | X31 != k6_domain_1(X31,X33)
        | v1_zfmisc_1(X31)
        | v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

cnf(c_0_55,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = u1_struct_0(esk4_0)
    | v1_zfmisc_1(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_56,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(k1_tex_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_32]),c_0_27])])).

fof(c_0_58,plain,(
    ! [X21] :
      ( v7_struct_0(X21)
      | ~ l1_struct_0(X21)
      | ~ v1_zfmisc_1(u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).

cnf(c_0_59,plain,
    ( v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X2 != k6_domain_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = u1_struct_0(esk4_0)
    | v1_zfmisc_1(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

fof(c_0_61,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,X27)
      | m1_subset_1(u1_struct_0(X28),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_62,plain,
    ( v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_26])])).

cnf(c_0_64,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_65,plain,(
    ! [X20] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | ~ v1_xboole_0(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_66,negated_conjecture,
    ( v7_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_67,plain,(
    ! [X29,X30] :
      ( ( ~ v1_xboole_0(X30)
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v7_struct_0(X29)
        | ~ l1_struct_0(X29) )
      & ( ~ v1_subset_1(X30,u1_struct_0(X29))
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v7_struct_0(X29)
        | ~ l1_struct_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tex_2])])])])])).

cnf(c_0_68,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_64])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( v7_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_56]),c_0_27])])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v7_struct_0(X2)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_32]),c_0_27])])).

cnf(c_0_73,negated_conjecture,
    ( v7_struct_0(esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_28])).

fof(c_0_74,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ m1_subset_1(X26,X25)
      | k6_domain_1(X25,X26) = k1_tarski(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_75,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_76,plain,(
    ! [X13] : m1_subset_1(k2_subset_1(X13),k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_77,plain,(
    ! [X12] : k2_subset_1(X12) = X12 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_78,plain,(
    ! [X4,X5,X6,X7,X8,X9] :
      ( ( ~ r2_hidden(X6,X5)
        | X6 = X4
        | X5 != k1_tarski(X4) )
      & ( X7 != X4
        | r2_hidden(X7,X5)
        | X5 != k1_tarski(X4) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | esk1_2(X8,X9) != X8
        | X9 = k1_tarski(X8) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | esk1_2(X8,X9) = X8
        | X9 = k1_tarski(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_28]),c_0_73])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_81,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_82,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X16))
      | ~ v1_xboole_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_83,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_56]),c_0_27])])).

cnf(c_0_87,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_89,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_85,c_0_81])).

cnf(c_0_91,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_64]),c_0_32]),c_0_27])])).

cnf(c_0_92,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_93,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = k2_tarski(esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_26])).

cnf(c_0_94,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_90])])).

cnf(c_0_96,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ l1_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | v1_subset_1(k2_tarski(esk5_0,esk5_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_98,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v2_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_56]),c_0_57])])).

cnf(c_0_100,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0)
    | ~ m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_97]),c_0_28]),c_0_98]),c_0_73])).

cnf(c_0_101,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ l1_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_99])).

cnf(c_0_102,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_103,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_56]),c_0_27])])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_93])).

cnf(c_0_105,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_106,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_56]),c_0_57])])).

cnf(c_0_107,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_102]),c_0_64])).

cnf(c_0_108,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_27]),c_0_26])]),c_0_28])).

cnf(c_0_110,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X2))
    | ~ v1_tex_2(X2,X1)
    | ~ v7_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_107]),c_0_64]),c_0_56])).

cnf(c_0_111,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( v7_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[c_0_70,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112]),c_0_32]),c_0_27])]),c_0_28])).

cnf(c_0_114,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_99]),c_0_109])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_114]),c_0_27]),c_0_26])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:31:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.14/0.39  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.028 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 0.14/0.39  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.14/0.39  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.14/0.39  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.14/0.39  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.14/0.39  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.14/0.39  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.14/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.14/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.39  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 0.14/0.39  fof(fc6_struct_0, axiom, ![X1]:((~(v7_struct_0(X1))&l1_struct_0(X1))=>~(v1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 0.14/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.14/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.39  fof(cc6_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v7_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~(v1_xboole_0(X2))=>(~(v1_xboole_0(X2))&~(v1_subset_1(X2,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tex_2)).
% 0.14/0.39  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.14/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.14/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.14/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.14/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.14/0.39  fof(c_0_20, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.14/0.39  fof(c_0_21, plain, ![X40, X41]:(((~v2_struct_0(k1_tex_2(X40,X41))|(v2_struct_0(X40)|~l1_pre_topc(X40)|~m1_subset_1(X41,u1_struct_0(X40))))&(v1_pre_topc(k1_tex_2(X40,X41))|(v2_struct_0(X40)|~l1_pre_topc(X40)|~m1_subset_1(X41,u1_struct_0(X40)))))&(m1_pre_topc(k1_tex_2(X40,X41),X40)|(v2_struct_0(X40)|~l1_pre_topc(X40)|~m1_subset_1(X41,u1_struct_0(X40))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.14/0.39  fof(c_0_22, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&((~v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)))&(v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.14/0.39  fof(c_0_23, plain, ![X23, X24]:(v1_xboole_0(X23)|~m1_subset_1(X24,X23)|m1_subset_1(k6_domain_1(X23,X24),k1_zfmisc_1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.14/0.39  fof(c_0_24, plain, ![X34, X35, X36]:((~v1_tex_2(X35,X34)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|(X36!=u1_struct_0(X35)|v1_subset_1(X36,u1_struct_0(X34))))|~m1_pre_topc(X35,X34)|~l1_pre_topc(X34))&((m1_subset_1(esk3_2(X34,X35),k1_zfmisc_1(u1_struct_0(X34)))|v1_tex_2(X35,X34)|~m1_pre_topc(X35,X34)|~l1_pre_topc(X34))&((esk3_2(X34,X35)=u1_struct_0(X35)|v1_tex_2(X35,X34)|~m1_pre_topc(X35,X34)|~l1_pre_topc(X34))&(~v1_subset_1(esk3_2(X34,X35),u1_struct_0(X34))|v1_tex_2(X35,X34)|~m1_pre_topc(X35,X34)|~l1_pre_topc(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.14/0.39  cnf(c_0_25, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  fof(c_0_29, plain, ![X38, X39]:((~v1_subset_1(X39,X38)|X39!=X38|~m1_subset_1(X39,k1_zfmisc_1(X38)))&(X39=X38|v1_subset_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.14/0.39  cnf(c_0_30, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.39  cnf(c_0_31, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (m1_pre_topc(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])]), c_0_28])).
% 0.14/0.39  cnf(c_0_33, plain, (esk3_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_34, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.14/0.39  cnf(c_0_36, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|m1_subset_1(esk3_2(esk4_0,k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_27])])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (esk3_2(esk4_0,k1_tex_2(esk4_0,esk5_0))=u1_struct_0(k1_tex_2(esk4_0,esk5_0))|v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_32]), c_0_27])])).
% 0.14/0.39  cnf(c_0_38, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, (~v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_40, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=u1_struct_0(esk4_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.39  cnf(c_0_41, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|m1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|~v1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_37]), c_0_32]), c_0_27])])).
% 0.14/0.39  fof(c_0_43, plain, ![X42, X43]:(((~v2_struct_0(k1_tex_2(X42,X43))|(v2_struct_0(X42)|~l1_pre_topc(X42)|~m1_subset_1(X43,u1_struct_0(X42))))&(v7_struct_0(k1_tex_2(X42,X43))|(v2_struct_0(X42)|~l1_pre_topc(X42)|~m1_subset_1(X43,u1_struct_0(X42)))))&(v1_pre_topc(k1_tex_2(X42,X43))|(v2_struct_0(X42)|~l1_pre_topc(X42)|~m1_subset_1(X43,u1_struct_0(X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.14/0.39  fof(c_0_44, plain, ![X22]:(~v7_struct_0(X22)|~l1_struct_0(X22)|v1_zfmisc_1(u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.14/0.39  cnf(c_0_45, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=u1_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))|~v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.39  cnf(c_0_46, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_41]), c_0_42])).
% 0.14/0.39  cnf(c_0_47, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.39  fof(c_0_48, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,X18)|l1_pre_topc(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.14/0.39  cnf(c_0_49, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.14/0.39  cnf(c_0_50, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|k6_domain_1(u1_struct_0(esk4_0),esk5_0)=u1_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.39  cnf(c_0_51, negated_conjecture, (v7_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_26]), c_0_27])]), c_0_28])).
% 0.14/0.39  fof(c_0_52, plain, ![X17]:(~l1_pre_topc(X17)|l1_struct_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.39  cnf(c_0_53, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.14/0.39  fof(c_0_54, plain, ![X31, X33]:(((m1_subset_1(esk2_1(X31),X31)|~v1_zfmisc_1(X31)|v1_xboole_0(X31))&(X31=k6_domain_1(X31,esk2_1(X31))|~v1_zfmisc_1(X31)|v1_xboole_0(X31)))&(~m1_subset_1(X33,X31)|X31!=k6_domain_1(X31,X33)|v1_zfmisc_1(X31)|v1_xboole_0(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.14/0.39  cnf(c_0_55, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=u1_struct_0(esk4_0)|v1_zfmisc_1(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.14/0.39  cnf(c_0_56, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.14/0.39  cnf(c_0_57, negated_conjecture, (l1_pre_topc(k1_tex_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_32]), c_0_27])])).
% 0.14/0.39  fof(c_0_58, plain, ![X21]:(v7_struct_0(X21)|~l1_struct_0(X21)|~v1_zfmisc_1(u1_struct_0(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).
% 0.14/0.39  cnf(c_0_59, plain, (v1_zfmisc_1(X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)|X2!=k6_domain_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.14/0.39  cnf(c_0_60, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=u1_struct_0(esk4_0)|v1_zfmisc_1(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.14/0.39  fof(c_0_61, plain, ![X27, X28]:(~l1_pre_topc(X27)|(~m1_pre_topc(X28,X27)|m1_subset_1(u1_struct_0(X28),k1_zfmisc_1(u1_struct_0(X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.14/0.39  cnf(c_0_62, plain, (v7_struct_0(X1)|~l1_struct_0(X1)|~v1_zfmisc_1(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.39  cnf(c_0_63, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_26])])).
% 0.14/0.39  cnf(c_0_64, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.14/0.39  fof(c_0_65, plain, ![X20]:(v2_struct_0(X20)|~l1_struct_0(X20)|~v1_xboole_0(u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.39  cnf(c_0_66, negated_conjecture, (v7_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.14/0.39  fof(c_0_67, plain, ![X29, X30]:((~v1_xboole_0(X30)|v1_xboole_0(X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v7_struct_0(X29)|~l1_struct_0(X29)))&(~v1_subset_1(X30,u1_struct_0(X29))|v1_xboole_0(X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v7_struct_0(X29)|~l1_struct_0(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tex_2])])])])])).
% 0.14/0.39  cnf(c_0_68, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_34, c_0_64])).
% 0.14/0.39  cnf(c_0_69, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.14/0.39  cnf(c_0_70, negated_conjecture, (v7_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_56]), c_0_27])])).
% 0.14/0.39  cnf(c_0_71, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|~v1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v7_struct_0(X2)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.14/0.39  cnf(c_0_72, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_32]), c_0_27])])).
% 0.14/0.39  cnf(c_0_73, negated_conjecture, (v7_struct_0(esk4_0)|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_28])).
% 0.14/0.39  fof(c_0_74, plain, ![X25, X26]:(v1_xboole_0(X25)|~m1_subset_1(X26,X25)|k6_domain_1(X25,X26)=k1_tarski(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.14/0.39  fof(c_0_75, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.39  fof(c_0_76, plain, ![X13]:m1_subset_1(k2_subset_1(X13),k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.14/0.39  fof(c_0_77, plain, ![X12]:k2_subset_1(X12)=X12, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.14/0.39  fof(c_0_78, plain, ![X4, X5, X6, X7, X8, X9]:(((~r2_hidden(X6,X5)|X6=X4|X5!=k1_tarski(X4))&(X7!=X4|r2_hidden(X7,X5)|X5!=k1_tarski(X4)))&((~r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)!=X8|X9=k1_tarski(X8))&(r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)=X8|X9=k1_tarski(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.14/0.39  cnf(c_0_79, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))|~l1_struct_0(esk4_0)|~m1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_28]), c_0_73])).
% 0.14/0.39  cnf(c_0_80, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.14/0.39  cnf(c_0_81, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.14/0.39  fof(c_0_82, plain, ![X14, X15, X16]:(~r2_hidden(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X16))|~v1_xboole_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.14/0.39  cnf(c_0_83, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.14/0.39  cnf(c_0_84, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.14/0.39  cnf(c_0_85, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.14/0.39  cnf(c_0_86, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))|~m1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_56]), c_0_27])])).
% 0.14/0.39  cnf(c_0_87, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 0.14/0.39  cnf(c_0_88, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.14/0.39  cnf(c_0_89, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 0.14/0.39  cnf(c_0_90, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_85, c_0_81])).
% 0.14/0.39  cnf(c_0_91, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_64]), c_0_32]), c_0_27])])).
% 0.14/0.39  cnf(c_0_92, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_93, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=k2_tarski(esk5_0,esk5_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_87, c_0_26])).
% 0.14/0.39  cnf(c_0_94, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.14/0.39  cnf(c_0_95, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_90])])).
% 0.14/0.39  cnf(c_0_96, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v2_struct_0(k1_tex_2(esk4_0,esk5_0))|~l1_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_69, c_0_91])).
% 0.14/0.39  cnf(c_0_97, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_subset_1(k2_tarski(esk5_0,esk5_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.14/0.39  cnf(c_0_98, plain, (~v1_xboole_0(k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.14/0.39  cnf(c_0_99, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v2_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_56]), c_0_57])])).
% 0.14/0.39  cnf(c_0_100, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)|~m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_97]), c_0_28]), c_0_98]), c_0_73])).
% 0.14/0.39  cnf(c_0_101, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))|~l1_struct_0(k1_tex_2(esk4_0,esk5_0))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_69, c_0_99])).
% 0.14/0.39  cnf(c_0_102, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_103, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))|~m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_56]), c_0_27])])).
% 0.14/0.39  cnf(c_0_104, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_35, c_0_93])).
% 0.14/0.39  cnf(c_0_105, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_106, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_56]), c_0_57])])).
% 0.14/0.39  cnf(c_0_107, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_102]), c_0_64])).
% 0.14/0.39  cnf(c_0_108, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.14/0.39  cnf(c_0_109, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_27]), c_0_26])]), c_0_28])).
% 0.14/0.39  cnf(c_0_110, plain, (v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X2))|~v1_tex_2(X2,X1)|~v7_struct_0(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_107]), c_0_64]), c_0_56])).
% 0.14/0.39  cnf(c_0_111, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[c_0_108, c_0_109])).
% 0.14/0.39  cnf(c_0_112, negated_conjecture, (v7_struct_0(esk4_0)), inference(sr,[status(thm)],[c_0_70, c_0_109])).
% 0.14/0.39  cnf(c_0_113, negated_conjecture, (v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112]), c_0_32]), c_0_27])]), c_0_28])).
% 0.14/0.39  cnf(c_0_114, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_99]), c_0_109])).
% 0.14/0.39  cnf(c_0_115, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_114]), c_0_27]), c_0_26])]), c_0_28]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 116
% 0.14/0.39  # Proof object clause steps            : 75
% 0.14/0.39  # Proof object formula steps           : 41
% 0.14/0.39  # Proof object conjectures             : 46
% 0.14/0.39  # Proof object clause conjectures      : 43
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 28
% 0.14/0.39  # Proof object initial formulas used   : 20
% 0.14/0.39  # Proof object generating inferences   : 40
% 0.14/0.39  # Proof object simplifying inferences  : 68
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 20
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 38
% 0.14/0.39  # Removed in clause preprocessing      : 3
% 0.14/0.39  # Initial clauses in saturation        : 35
% 0.14/0.39  # Processed clauses                    : 197
% 0.14/0.39  # ...of these trivial                  : 8
% 0.14/0.39  # ...subsumed                          : 29
% 0.14/0.39  # ...remaining for further processing  : 160
% 0.14/0.39  # Other redundant clauses eliminated   : 7
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 25
% 0.14/0.39  # Backward-rewritten                   : 18
% 0.14/0.39  # Generated clauses                    : 323
% 0.14/0.39  # ...of the previous two non-trivial   : 293
% 0.14/0.39  # Contextual simplify-reflections      : 10
% 0.14/0.39  # Paramodulations                      : 306
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 7
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 69
% 0.14/0.39  #    Positive orientable unit clauses  : 18
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 5
% 0.14/0.39  #    Non-unit-clauses                  : 46
% 0.14/0.39  # Current number of unprocessed clauses: 153
% 0.14/0.39  # ...number of literals in the above   : 681
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 89
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 1103
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 462
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 49
% 0.14/0.39  # Unit Clause-clause subsumption calls : 74
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 6
% 0.14/0.39  # BW rewrite match successes           : 5
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 8434
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.040 s
% 0.14/0.39  # System time              : 0.007 s
% 0.14/0.39  # Total time               : 0.047 s
% 0.14/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
