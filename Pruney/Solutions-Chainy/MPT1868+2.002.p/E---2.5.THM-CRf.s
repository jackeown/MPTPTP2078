%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:01 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 616 expanded)
%              Number of clauses        :   59 ( 261 expanded)
%              Number of leaves         :   17 ( 152 expanded)
%              Depth                    :   14
%              Number of atoms          :  339 (1957 expanded)
%              Number of equality atoms :   40 ( 248 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   21 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t36_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t10_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ? [X3] :
              ( ~ v2_struct_0(X3)
              & v1_pre_topc(X3)
              & m1_pre_topc(X3,X1)
              & X2 = u1_struct_0(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(d1_tex_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ( v7_struct_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & u1_struct_0(X1) = k6_domain_1(u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t26_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v2_tex_2(X3,X1)
                <=> v1_tdlat_3(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(cc25_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & v7_struct_0(X2)
              & v2_pre_topc(X2) )
           => ( ~ v2_struct_0(X2)
              & v1_tdlat_3(X2)
              & v2_tdlat_3(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc25_tex_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_17,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ m1_subset_1(X26,X25)
      | k6_domain_1(X25,X26) = k1_tarski(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_18,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t36_tex_2])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | m1_subset_1(k1_tarski(X13),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_21,plain,(
    ! [X12] : ~ v1_xboole_0(k1_tarski(X12)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ~ v2_tex_2(k6_domain_1(u1_struct_0(esk5_0),esk6_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_25,plain,(
    ! [X38,X39] :
      ( ( ~ v2_struct_0(esk4_2(X38,X39))
        | v1_xboole_0(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ l1_pre_topc(X38) )
      & ( v1_pre_topc(esk4_2(X38,X39))
        | v1_xboole_0(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_pre_topc(esk4_2(X38,X39),X38)
        | v1_xboole_0(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ l1_pre_topc(X38) )
      & ( X39 = u1_struct_0(esk4_2(X38,X39))
        | v1_xboole_0(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,X18)
      | v1_xboole_0(X18)
      | r2_hidden(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_29,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
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

cnf(c_0_32,plain,
    ( X1 = u1_struct_0(esk4_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k2_tarski(esk6_0,esk6_0) = k6_domain_1(u1_struct_0(esk5_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( m1_pre_topc(esk4_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( u1_struct_0(esk4_2(X1,k2_tarski(X2,X2))) = k2_tarski(X2,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | r2_hidden(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(X1))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_36])).

fof(c_0_44,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | l1_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | m1_pre_topc(esk4_2(X1,k2_tarski(X2,X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_34])).

fof(c_0_46,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | m1_subset_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_23])).

fof(c_0_48,plain,(
    ! [X19,X20] :
      ( ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | v2_pre_topc(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_49,plain,(
    ! [X32,X34] :
      ( ( m1_subset_1(esk2_1(X32),u1_struct_0(X32))
        | ~ v7_struct_0(X32)
        | v2_struct_0(X32)
        | ~ l1_struct_0(X32) )
      & ( u1_struct_0(X32) = k6_domain_1(u1_struct_0(X32),esk2_1(X32))
        | ~ v7_struct_0(X32)
        | v2_struct_0(X32)
        | ~ l1_struct_0(X32) )
      & ( ~ m1_subset_1(X34,u1_struct_0(X32))
        | u1_struct_0(X32) != k6_domain_1(u1_struct_0(X32),X34)
        | v7_struct_0(X32)
        | v2_struct_0(X32)
        | ~ l1_struct_0(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_1])])])])])])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(esk4_2(esk5_0,k2_tarski(esk6_0,esk6_0))) = k2_tarski(esk6_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk4_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_xboole_0(k6_domain_1(u1_struct_0(esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_54,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(esk4_2(esk5_0,k2_tarski(esk6_0,esk6_0)),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).

cnf(c_0_58,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_60,plain,
    ( v7_struct_0(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X2),X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))) = k6_domain_1(u1_struct_0(esk5_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v2_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_41])]),c_0_42]),c_0_53])).

fof(c_0_63,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_64,negated_conjecture,
    ( l1_pre_topc(esk4_2(esk5_0,k2_tarski(esk6_0,esk6_0)))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_41])])).

cnf(c_0_65,plain,
    ( m1_subset_1(X1,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_66,plain,(
    ! [X41,X42,X43] :
      ( ( ~ v2_tex_2(X43,X41)
        | v1_tdlat_3(X42)
        | X43 != u1_struct_0(X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ l1_pre_topc(X41) )
      & ( ~ v1_tdlat_3(X42)
        | v2_tex_2(X43,X41)
        | X43 != u1_struct_0(X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

fof(c_0_67,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,X27)
      | m1_subset_1(u1_struct_0(X28),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_68,plain,(
    ! [X30,X31] :
      ( ( ~ v2_struct_0(X31)
        | v2_struct_0(X31)
        | ~ v7_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30) )
      & ( v1_tdlat_3(X31)
        | v2_struct_0(X31)
        | ~ v7_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30) )
      & ( v2_tdlat_3(X31)
        | v2_struct_0(X31)
        | ~ v7_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc25_tex_2])])])])])).

cnf(c_0_69,negated_conjecture,
    ( v2_pre_topc(esk4_2(esk5_0,k2_tarski(esk6_0,esk6_0)))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_55]),c_0_41]),c_0_59])])).

cnf(c_0_70,negated_conjecture,
    ( v7_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | k6_domain_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),X1) != k6_domain_1(u1_struct_0(esk5_0),esk6_0)
    | ~ l1_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))
    | ~ m1_subset_1(X1,k6_domain_1(u1_struct_0(esk5_0),esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_71,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( l1_pre_topc(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_36])).

cnf(c_0_73,plain,
    ( k6_domain_1(k2_tarski(X1,X1),X1) = k2_tarski(X1,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_65]),c_0_34])).

cnf(c_0_74,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v7_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( m1_pre_topc(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_36])).

cnf(c_0_78,negated_conjecture,
    ( v2_pre_topc(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_36])).

cnf(c_0_79,negated_conjecture,
    ( v7_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | k6_domain_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),X1) != k6_domain_1(u1_struct_0(esk5_0),esk6_0)
    | ~ m1_subset_1(X1,k6_domain_1(u1_struct_0(esk5_0),esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk6_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_36])).

cnf(c_0_81,negated_conjecture,
    ( k6_domain_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),esk6_0) = k6_domain_1(u1_struct_0(esk5_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_36])).

cnf(c_0_82,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]),c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( v1_tdlat_3(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v7_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_41])]),c_0_42]),c_0_78]),c_0_62])).

cnf(c_0_84,negated_conjecture,
    ( v7_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

fof(c_0_85,plain,(
    ! [X24] :
      ( v2_struct_0(X24)
      | ~ l1_struct_0(X24)
      | ~ v1_xboole_0(u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_86,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_tdlat_3(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_77]),c_0_41])]),c_0_42]),c_0_62])).

cnf(c_0_87,negated_conjecture,
    ( v1_tdlat_3(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_88,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))),esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(esk5_0),esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_91,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_71])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_61]),c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_41])]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.51  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.030 s
% 0.20/0.51  # Presaturation interreduction done
% 0.20/0.51  
% 0.20/0.51  # Proof found!
% 0.20/0.51  # SZS status Theorem
% 0.20/0.51  # SZS output start CNFRefutation
% 0.20/0.51  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.20/0.51  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.51  fof(t36_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 0.20/0.51  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.20/0.51  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.20/0.51  fof(t10_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>?[X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&X2=u1_struct_0(X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 0.20/0.51  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.51  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.51  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.51  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.51  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.51  fof(d1_tex_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>(v7_struct_0(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&u1_struct_0(X1)=k6_domain_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_1)).
% 0.20/0.51  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.51  fof(t26_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v2_tex_2(X3,X1)<=>v1_tdlat_3(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 0.20/0.51  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.51  fof(cc25_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(((~(v2_struct_0(X2))&v7_struct_0(X2))&v2_pre_topc(X2))=>((~(v2_struct_0(X2))&v1_tdlat_3(X2))&v2_tdlat_3(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc25_tex_2)).
% 0.20/0.51  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.51  fof(c_0_17, plain, ![X25, X26]:(v1_xboole_0(X25)|~m1_subset_1(X26,X25)|k6_domain_1(X25,X26)=k1_tarski(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.20/0.51  fof(c_0_18, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.51  fof(c_0_19, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)))), inference(assume_negation,[status(cth)],[t36_tex_2])).
% 0.20/0.51  fof(c_0_20, plain, ![X13, X14]:(~r2_hidden(X13,X14)|m1_subset_1(k1_tarski(X13),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.20/0.51  fof(c_0_21, plain, ![X12]:~v1_xboole_0(k1_tarski(X12)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.20/0.51  cnf(c_0_22, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.51  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.51  fof(c_0_24, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&~v2_tex_2(k6_domain_1(u1_struct_0(esk5_0),esk6_0),esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.20/0.51  fof(c_0_25, plain, ![X38, X39]:((((~v2_struct_0(esk4_2(X38,X39))|(v1_xboole_0(X39)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38))))|(v2_struct_0(X38)|~l1_pre_topc(X38)))&(v1_pre_topc(esk4_2(X38,X39))|(v1_xboole_0(X39)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38))))|(v2_struct_0(X38)|~l1_pre_topc(X38))))&(m1_pre_topc(esk4_2(X38,X39),X38)|(v1_xboole_0(X39)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38))))|(v2_struct_0(X38)|~l1_pre_topc(X38))))&(X39=u1_struct_0(esk4_2(X38,X39))|(v1_xboole_0(X39)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38))))|(v2_struct_0(X38)|~l1_pre_topc(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).
% 0.20/0.51  cnf(c_0_26, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.51  cnf(c_0_27, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.51  fof(c_0_28, plain, ![X17, X18]:(~m1_subset_1(X17,X18)|(v1_xboole_0(X18)|r2_hidden(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.51  cnf(c_0_29, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.51  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.51  fof(c_0_31, plain, ![X4, X5, X6, X7, X8, X9]:(((~r2_hidden(X6,X5)|X6=X4|X5!=k1_tarski(X4))&(X7!=X4|r2_hidden(X7,X5)|X5!=k1_tarski(X4)))&((~r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)!=X8|X9=k1_tarski(X8))&(r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)=X8|X9=k1_tarski(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.51  cnf(c_0_32, plain, (X1=u1_struct_0(esk4_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.51  cnf(c_0_33, plain, (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_23])).
% 0.20/0.51  cnf(c_0_34, plain, (~v1_xboole_0(k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_27, c_0_23])).
% 0.20/0.51  cnf(c_0_35, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.51  cnf(c_0_36, negated_conjecture, (k2_tarski(esk6_0,esk6_0)=k6_domain_1(u1_struct_0(esk5_0),esk6_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.51  cnf(c_0_37, plain, (m1_pre_topc(esk4_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.51  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.51  cnf(c_0_39, plain, (u1_struct_0(esk4_2(X1,k2_tarski(X2,X2)))=k2_tarski(X2,X2)|v2_struct_0(X1)|~l1_pre_topc(X1)|~r2_hidden(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.20/0.51  cnf(c_0_40, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|r2_hidden(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_35, c_0_30])).
% 0.20/0.51  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.51  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.51  cnf(c_0_43, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(X1))|v1_xboole_0(u1_struct_0(esk5_0))|~r2_hidden(esk6_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_36])).
% 0.20/0.51  fof(c_0_44, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|l1_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.51  cnf(c_0_45, plain, (v2_struct_0(X1)|m1_pre_topc(esk4_2(X1,k2_tarski(X2,X2)),X1)|~l1_pre_topc(X1)|~r2_hidden(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_34])).
% 0.20/0.51  fof(c_0_46, plain, ![X15, X16]:(~r2_hidden(X15,X16)|m1_subset_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.51  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_38, c_0_23])).
% 0.20/0.51  fof(c_0_48, plain, ![X19, X20]:(~v2_pre_topc(X19)|~l1_pre_topc(X19)|(~m1_pre_topc(X20,X19)|v2_pre_topc(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.51  fof(c_0_49, plain, ![X32, X34]:(((m1_subset_1(esk2_1(X32),u1_struct_0(X32))|~v7_struct_0(X32)|(v2_struct_0(X32)|~l1_struct_0(X32)))&(u1_struct_0(X32)=k6_domain_1(u1_struct_0(X32),esk2_1(X32))|~v7_struct_0(X32)|(v2_struct_0(X32)|~l1_struct_0(X32))))&(~m1_subset_1(X34,u1_struct_0(X32))|u1_struct_0(X32)!=k6_domain_1(u1_struct_0(X32),X34)|v7_struct_0(X32)|(v2_struct_0(X32)|~l1_struct_0(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_1])])])])])])).
% 0.20/0.51  cnf(c_0_50, negated_conjecture, (u1_struct_0(esk4_2(esk5_0,k2_tarski(esk6_0,esk6_0)))=k2_tarski(esk6_0,esk6_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])]), c_0_42])).
% 0.20/0.51  cnf(c_0_51, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk4_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.51  cnf(c_0_52, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_43, c_0_40])).
% 0.20/0.51  cnf(c_0_53, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~v1_xboole_0(k6_domain_1(u1_struct_0(esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 0.20/0.51  cnf(c_0_54, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.51  cnf(c_0_55, negated_conjecture, (m1_pre_topc(esk4_2(esk5_0,k2_tarski(esk6_0,esk6_0)),esk5_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_41])]), c_0_42])).
% 0.20/0.51  cnf(c_0_56, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.51  cnf(c_0_57, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).
% 0.20/0.51  cnf(c_0_58, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.51  cnf(c_0_59, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.51  cnf(c_0_60, plain, (v7_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|u1_struct_0(X2)!=k6_domain_1(u1_struct_0(X2),X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.51  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))=k6_domain_1(u1_struct_0(esk5_0),esk6_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_50, c_0_36])).
% 0.20/0.51  cnf(c_0_62, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~v2_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_41])]), c_0_42]), c_0_53])).
% 0.20/0.51  fof(c_0_63, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.51  cnf(c_0_64, negated_conjecture, (l1_pre_topc(esk4_2(esk5_0,k2_tarski(esk6_0,esk6_0)))|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_41])])).
% 0.20/0.51  cnf(c_0_65, plain, (m1_subset_1(X1,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.51  fof(c_0_66, plain, ![X41, X42, X43]:((~v2_tex_2(X43,X41)|v1_tdlat_3(X42)|X43!=u1_struct_0(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|(v2_struct_0(X42)|~m1_pre_topc(X42,X41))|(v2_struct_0(X41)|~l1_pre_topc(X41)))&(~v1_tdlat_3(X42)|v2_tex_2(X43,X41)|X43!=u1_struct_0(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|(v2_struct_0(X42)|~m1_pre_topc(X42,X41))|(v2_struct_0(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).
% 0.20/0.51  fof(c_0_67, plain, ![X27, X28]:(~l1_pre_topc(X27)|(~m1_pre_topc(X28,X27)|m1_subset_1(u1_struct_0(X28),k1_zfmisc_1(u1_struct_0(X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.51  fof(c_0_68, plain, ![X30, X31]:(((~v2_struct_0(X31)|(v2_struct_0(X31)|~v7_struct_0(X31)|~v2_pre_topc(X31))|~m1_pre_topc(X31,X30)|(v2_struct_0(X30)|~l1_pre_topc(X30)))&(v1_tdlat_3(X31)|(v2_struct_0(X31)|~v7_struct_0(X31)|~v2_pre_topc(X31))|~m1_pre_topc(X31,X30)|(v2_struct_0(X30)|~l1_pre_topc(X30))))&(v2_tdlat_3(X31)|(v2_struct_0(X31)|~v7_struct_0(X31)|~v2_pre_topc(X31))|~m1_pre_topc(X31,X30)|(v2_struct_0(X30)|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc25_tex_2])])])])])).
% 0.20/0.51  cnf(c_0_69, negated_conjecture, (v2_pre_topc(esk4_2(esk5_0,k2_tarski(esk6_0,esk6_0)))|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_55]), c_0_41]), c_0_59])])).
% 0.20/0.51  cnf(c_0_70, negated_conjecture, (v7_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))|v1_xboole_0(u1_struct_0(esk5_0))|k6_domain_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),X1)!=k6_domain_1(u1_struct_0(esk5_0),esk6_0)|~l1_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))|~m1_subset_1(X1,k6_domain_1(u1_struct_0(esk5_0),esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.20/0.51  cnf(c_0_71, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.51  cnf(c_0_72, negated_conjecture, (l1_pre_topc(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_64, c_0_36])).
% 0.20/0.51  cnf(c_0_73, plain, (k6_domain_1(k2_tarski(X1,X1),X1)=k2_tarski(X1,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_65]), c_0_34])).
% 0.20/0.51  cnf(c_0_74, plain, (v2_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X3)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.51  cnf(c_0_75, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.51  cnf(c_0_76, plain, (v1_tdlat_3(X1)|v2_struct_0(X1)|v2_struct_0(X2)|~v7_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.51  cnf(c_0_77, negated_conjecture, (m1_pre_topc(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),esk5_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_55, c_0_36])).
% 0.20/0.51  cnf(c_0_78, negated_conjecture, (v2_pre_topc(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_69, c_0_36])).
% 0.20/0.51  cnf(c_0_79, negated_conjecture, (v7_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))|v1_xboole_0(u1_struct_0(esk5_0))|k6_domain_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),X1)!=k6_domain_1(u1_struct_0(esk5_0),esk6_0)|~m1_subset_1(X1,k6_domain_1(u1_struct_0(esk5_0),esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.20/0.51  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk6_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_65, c_0_36])).
% 0.20/0.51  cnf(c_0_81, negated_conjecture, (k6_domain_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),esk6_0)=k6_domain_1(u1_struct_0(esk5_0),esk6_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_73, c_0_36])).
% 0.20/0.51  cnf(c_0_82, plain, (v2_tex_2(u1_struct_0(X1),X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]), c_0_75])).
% 0.20/0.51  cnf(c_0_83, negated_conjecture, (v1_tdlat_3(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))|v1_xboole_0(u1_struct_0(esk5_0))|~v7_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_41])]), c_0_42]), c_0_78]), c_0_62])).
% 0.20/0.51  cnf(c_0_84, negated_conjecture, (v7_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))|v1_xboole_0(u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.20/0.51  fof(c_0_85, plain, ![X24]:(v2_struct_0(X24)|~l1_struct_0(X24)|~v1_xboole_0(u1_struct_0(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.51  cnf(c_0_86, negated_conjecture, (v2_tex_2(u1_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))),esk5_0)|v1_xboole_0(u1_struct_0(esk5_0))|~v1_tdlat_3(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_77]), c_0_41])]), c_0_42]), c_0_62])).
% 0.20/0.51  cnf(c_0_87, negated_conjecture, (v1_tdlat_3(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.51  cnf(c_0_88, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.20/0.51  cnf(c_0_89, negated_conjecture, (v2_tex_2(u1_struct_0(esk4_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))),esk5_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.51  cnf(c_0_90, negated_conjecture, (~v2_tex_2(k6_domain_1(u1_struct_0(esk5_0),esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.51  cnf(c_0_91, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_88, c_0_71])).
% 0.20/0.52  cnf(c_0_92, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_61]), c_0_90])).
% 0.20/0.52  cnf(c_0_93, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_41])]), c_0_42]), ['proof']).
% 0.20/0.52  # SZS output end CNFRefutation
% 0.20/0.52  # Proof object total steps             : 94
% 0.20/0.52  # Proof object clause steps            : 59
% 0.20/0.52  # Proof object formula steps           : 35
% 0.20/0.52  # Proof object conjectures             : 33
% 0.20/0.52  # Proof object clause conjectures      : 30
% 0.20/0.52  # Proof object formula conjectures     : 3
% 0.20/0.52  # Proof object initial clauses used    : 23
% 0.20/0.52  # Proof object initial formulas used   : 17
% 0.20/0.52  # Proof object generating inferences   : 30
% 0.20/0.52  # Proof object simplifying inferences  : 42
% 0.20/0.52  # Training examples: 0 positive, 0 negative
% 0.20/0.52  # Parsed axioms                        : 19
% 0.20/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.52  # Initial clauses                      : 36
% 0.20/0.52  # Removed in clause preprocessing      : 2
% 0.20/0.52  # Initial clauses in saturation        : 34
% 0.20/0.52  # Processed clauses                    : 570
% 0.20/0.52  # ...of these trivial                  : 2
% 0.20/0.52  # ...subsumed                          : 202
% 0.20/0.52  # ...remaining for further processing  : 366
% 0.20/0.52  # Other redundant clauses eliminated   : 73
% 0.20/0.52  # Clauses deleted for lack of memory   : 0
% 0.20/0.52  # Backward-subsumed                    : 11
% 0.20/0.52  # Backward-rewritten                   : 118
% 0.20/0.52  # Generated clauses                    : 5875
% 0.20/0.52  # ...of the previous two non-trivial   : 5625
% 0.20/0.52  # Contextual simplify-reflections      : 46
% 0.20/0.52  # Paramodulations                      : 5789
% 0.20/0.52  # Factorizations                       : 14
% 0.20/0.52  # Equation resolutions                 : 73
% 0.20/0.52  # Propositional unsat checks           : 0
% 0.20/0.52  #    Propositional check models        : 0
% 0.20/0.52  #    Propositional check unsatisfiable : 0
% 0.20/0.52  #    Propositional clauses             : 0
% 0.20/0.52  #    Propositional clauses after purity: 0
% 0.20/0.52  #    Propositional unsat core size     : 0
% 0.20/0.52  #    Propositional preprocessing time  : 0.000
% 0.20/0.52  #    Propositional encoding time       : 0.000
% 0.20/0.52  #    Propositional solver time         : 0.000
% 0.20/0.52  #    Success case prop preproc time    : 0.000
% 0.20/0.52  #    Success case prop encoding time   : 0.000
% 0.20/0.52  #    Success case prop solver time     : 0.000
% 0.20/0.52  # Current number of processed clauses  : 199
% 0.20/0.52  #    Positive orientable unit clauses  : 15
% 0.20/0.52  #    Positive unorientable unit clauses: 0
% 0.20/0.52  #    Negative unit clauses             : 3
% 0.20/0.52  #    Non-unit-clauses                  : 181
% 0.20/0.52  # Current number of unprocessed clauses: 5108
% 0.20/0.52  # ...number of literals in the above   : 34137
% 0.20/0.52  # Current number of archived formulas  : 0
% 0.20/0.52  # Current number of archived clauses   : 164
% 0.20/0.52  # Clause-clause subsumption calls (NU) : 15960
% 0.20/0.52  # Rec. Clause-clause subsumption calls : 3869
% 0.20/0.52  # Non-unit clause-clause subsumptions  : 253
% 0.20/0.52  # Unit Clause-clause subsumption calls : 135
% 0.20/0.52  # Rewrite failures with RHS unbound    : 0
% 0.20/0.52  # BW rewrite match attempts            : 6
% 0.20/0.52  # BW rewrite match successes           : 4
% 0.20/0.52  # Condensation attempts                : 0
% 0.20/0.52  # Condensation successes               : 0
% 0.20/0.52  # Termbank termtop insertions          : 130853
% 0.20/0.52  
% 0.20/0.52  # -------------------------------------------------
% 0.20/0.52  # User time                : 0.161 s
% 0.20/0.52  # System time              : 0.010 s
% 0.20/0.52  # Total time               : 0.171 s
% 0.20/0.52  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
