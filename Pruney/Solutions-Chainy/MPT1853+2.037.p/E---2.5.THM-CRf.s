%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:30 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  170 (11390 expanded)
%              Number of clauses        :  125 (4630 expanded)
%              Number of leaves         :   22 (2809 expanded)
%              Depth                    :   39
%              Number of atoms          :  507 (46185 expanded)
%              Number of equality atoms :   70 (3186 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

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

fof(t8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
              & v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t6_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_23,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X18,X17)
        | r2_hidden(X18,X17)
        | v1_xboole_0(X17) )
      & ( ~ r2_hidden(X18,X17)
        | m1_subset_1(X18,X17)
        | v1_xboole_0(X17) )
      & ( ~ m1_subset_1(X18,X17)
        | v1_xboole_0(X18)
        | ~ v1_xboole_0(X17) )
      & ( ~ v1_xboole_0(X18)
        | m1_subset_1(X18,X17)
        | ~ v1_xboole_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_24,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_25,plain,(
    ! [X41,X42] :
      ( ( ~ v2_struct_0(k1_tex_2(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_pre_topc(X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41)) )
      & ( v1_pre_topc(k1_tex_2(X41,X42))
        | v2_struct_0(X41)
        | ~ l1_pre_topc(X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41)) )
      & ( m1_pre_topc(k1_tex_2(X41,X42),X41)
        | v2_struct_0(X41)
        | ~ l1_pre_topc(X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ( ~ v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) )
    & ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

fof(c_0_27,plain,(
    ! [X47,X48] :
      ( v1_xboole_0(X47)
      | v1_zfmisc_1(X47)
      | ~ m1_subset_1(X48,X47)
      | v1_subset_1(k6_domain_1(X47,X48),X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).

fof(c_0_28,plain,(
    ! [X16] :
      ( ~ v1_xboole_0(X16)
      | v1_zfmisc_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v1_tex_2(X36,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | X37 != u1_struct_0(X36)
        | v1_subset_1(X37,u1_struct_0(X35))
        | ~ m1_pre_topc(X36,X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk3_2(X35,X36),k1_zfmisc_1(u1_struct_0(X35)))
        | v1_tex_2(X36,X35)
        | ~ m1_pre_topc(X36,X35)
        | ~ l1_pre_topc(X35) )
      & ( esk3_2(X35,X36) = u1_struct_0(X36)
        | v1_tex_2(X36,X35)
        | ~ m1_pre_topc(X36,X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ v1_subset_1(esk3_2(X35,X36),u1_struct_0(X35))
        | v1_tex_2(X36,X35)
        | ~ m1_pre_topc(X36,X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

cnf(c_0_32,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_42,plain,
    ( esk3_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X49,X50] :
      ( v2_struct_0(X49)
      | ~ l1_struct_0(X49)
      | ~ m1_subset_1(X50,u1_struct_0(X49))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X49),X50),u1_struct_0(X49))
      | ~ v7_struct_0(X49) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

cnf(c_0_44,plain,
    ( v1_subset_1(k6_domain_1(X1,X2),X1)
    | v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_46,plain,(
    ! [X39,X40] :
      ( ( ~ v1_subset_1(X40,X39)
        | X40 != X39
        | ~ m1_subset_1(X40,k1_zfmisc_1(X39)) )
      & ( X40 = X39
        | v1_subset_1(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_47,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | m1_subset_1(esk3_2(esk4_0,k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_34])])).

cnf(c_0_48,negated_conjecture,
    ( esk3_2(esk4_0,k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(k1_tex_2(esk4_0,esk5_0))
    | v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_34])])).

cnf(c_0_49,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( v1_subset_1(k6_domain_1(X1,esk1_1(X1)),X1)
    | v1_zfmisc_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))
    | v1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_33])).

cnf(c_0_54,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | m1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_48]),c_0_41]),c_0_34])])).

fof(c_0_57,plain,(
    ! [X43,X44] :
      ( ( ~ v2_struct_0(k1_tex_2(X43,X44))
        | v2_struct_0(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43)) )
      & ( v7_struct_0(k1_tex_2(X43,X44))
        | v2_struct_0(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43)) )
      & ( v1_pre_topc(k1_tex_2(X43,X44))
        | v2_struct_0(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

fof(c_0_58,plain,(
    ! [X29,X30] :
      ( v1_xboole_0(X29)
      | ~ m1_subset_1(X30,X29)
      | m1_subset_1(k6_domain_1(X29,X30),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(esk1_1(u1_struct_0(X1)),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk4_0))
    | ~ v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_62,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_63,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,X26)
      | l1_pre_topc(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_64,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X8
        | X9 != k1_tarski(X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_tarski(X8) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | esk2_2(X12,X13) != X12
        | X13 = k1_tarski(X12) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | esk2_2(X12,X13) = X12
        | X13 = k1_tarski(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_65,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_45]),c_0_37])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( v7_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_33]),c_0_34])]),c_0_35])).

fof(c_0_70,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | l1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_71,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_74,plain,(
    ! [X31,X32] :
      ( v1_xboole_0(X31)
      | ~ m1_subset_1(X32,X31)
      | k6_domain_1(X31,X32) = k1_tarski(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_75,plain,(
    ! [X45,X46] :
      ( v1_xboole_0(X45)
      | ~ m1_subset_1(X46,X45)
      | ~ v1_subset_1(k6_domain_1(X45,X46),X45)
      | ~ v1_zfmisc_1(X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_33])).

cnf(c_0_77,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | v1_zfmisc_1(u1_struct_0(esk4_0))
    | ~ l1_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])])).

cnf(c_0_78,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( l1_pre_topc(k1_tex_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_41]),c_0_34])])).

cnf(c_0_80,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = u1_struct_0(esk4_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_76])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | v1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_87,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_80,c_0_73])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_81])])).

cnf(c_0_89,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_82,c_0_73])).

cnf(c_0_90,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = u1_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_33])])).

cnf(c_0_91,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_34]),c_0_33])]),c_0_35])).

cnf(c_0_92,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_93,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = k2_tarski(esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_33])).

cnf(c_0_95,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = u1_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

fof(c_0_96,plain,(
    ! [X28] :
      ( v2_struct_0(X28)
      | ~ l1_struct_0(X28)
      | ~ v1_xboole_0(u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_97,plain,
    ( esk1_1(k2_tarski(X1,X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_39]),c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( k2_tarski(esk5_0,esk5_0) = u1_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,plain,
    ( k2_tarski(esk1_1(X1),esk1_1(X1)) = k6_domain_1(X1,esk1_1(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_45])).

cnf(c_0_100,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( esk1_1(u1_struct_0(esk4_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,plain,
    ( X1 = esk1_1(X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,k6_domain_1(X2,esk1_1(X2))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( esk1_1(u1_struct_0(esk4_0)) = esk5_0
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_35])).

cnf(c_0_104,negated_conjecture,
    ( X1 = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0)
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_105,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k6_domain_1(X1,esk1_1(X1))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( X1 = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_78]),c_0_34])])).

cnf(c_0_107,plain,
    ( r2_hidden(esk1_1(X1),k6_domain_1(X1,esk1_1(X1)))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0)
    | ~ v1_xboole_0(k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( esk1_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0)) = esk5_0
    | v1_xboole_0(k6_domain_1(u1_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_39])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_103])).

cnf(c_0_111,negated_conjecture,
    ( esk1_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_78]),c_0_34])])).

cnf(c_0_113,plain,
    ( m1_subset_1(k6_domain_1(X1,esk1_1(X1)),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_45])).

cnf(c_0_114,negated_conjecture,
    ( esk1_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_78]),c_0_34])])).

cnf(c_0_115,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(k6_domain_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk5_0),k1_zfmisc_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])).

cnf(c_0_117,negated_conjecture,
    ( k6_domain_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk5_0) = k2_tarski(esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_114]),c_0_115])).

fof(c_0_118,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ r2_hidden(X23,X22)
      | r2_hidden(X23,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_120,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_98])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_30])).

fof(c_0_123,plain,(
    ! [X24] : ~ v1_subset_1(k2_subset_1(X24),X24) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

fof(c_0_124,plain,(
    ! [X19] : k2_subset_1(X19) = X19 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(X1,k2_tarski(esk5_0,esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_94]),c_0_30])).

cnf(c_0_126,plain,
    ( m1_subset_1(X1,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_88])).

cnf(c_0_127,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_128,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(X1,k2_tarski(esk5_0,esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_125])).

cnf(c_0_130,plain,
    ( k6_domain_1(k2_tarski(X1,X1),X1) = k2_tarski(X1,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_126]),c_0_93])).

cnf(c_0_131,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_132,negated_conjecture,
    ( k6_domain_1(k2_tarski(esk5_0,esk5_0),X1) = k2_tarski(X1,X1)
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_129]),c_0_93])).

cnf(c_0_133,plain,
    ( v1_zfmisc_1(k2_tarski(X1,X1)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_97]),c_0_130]),c_0_131])).

cnf(c_0_134,negated_conjecture,
    ( ~ v1_subset_1(k2_tarski(X1,X1),k2_tarski(esk5_0,esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_132]),c_0_133])]),c_0_93]),c_0_129])).

fof(c_0_135,plain,(
    ! [X33,X34] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_pre_topc(X34,X33)
      | m1_subset_1(u1_struct_0(X34),k1_zfmisc_1(u1_struct_0(X33))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_136,negated_conjecture,
    ( ~ v1_subset_1(k2_tarski(X1,X1),u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_98]),c_0_30])).

cnf(c_0_137,plain,
    ( k6_domain_1(X1,esk1_1(X1)) = X1
    | v1_subset_1(k6_domain_1(X1,esk1_1(X1)),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_113])).

cnf(c_0_138,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_135])).

cnf(c_0_139,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(k6_domain_1(X1,esk1_1(X1)),u1_struct_0(esk4_0))
    | ~ r2_hidden(esk1_1(X1),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_136,c_0_99])).

cnf(c_0_140,plain,
    ( k6_domain_1(X1,esk1_1(X1)) = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_137]),c_0_45])).

cnf(c_0_141,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_138])).

cnf(c_0_142,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_struct_0(X3)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_138])).

cnf(c_0_143,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ v1_zfmisc_1(X1)
    | ~ r2_hidden(esk1_1(X1),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_144,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_41]),c_0_34])])).

cnf(c_0_145,plain,
    ( r2_hidden(esk1_1(u1_struct_0(X1)),u1_struct_0(X2))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_142,c_0_39])).

cnf(c_0_146,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))
    | ~ r2_hidden(esk1_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0))),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_143,c_0_144])).

cnf(c_0_147,negated_conjecture,
    ( r2_hidden(esk1_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0))),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_41]),c_0_34])])).

cnf(c_0_148,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ l1_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ r2_hidden(esk1_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0))),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_67]),c_0_69])]),c_0_100])).

cnf(c_0_149,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_147])).

cnf(c_0_150,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ r2_hidden(esk1_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0))),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_78]),c_0_79])])).

cnf(c_0_151,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_152,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ l1_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_149])).

cnf(c_0_153,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_154,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_150,c_0_147])).

cnf(c_0_155,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_151]),c_0_33])])).

cnf(c_0_156,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_78]),c_0_79])])).

cnf(c_0_157,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_158,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_153]),c_0_138])).

cnf(c_0_159,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ l1_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_154])).

cnf(c_0_160,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_155,c_0_91])])).

cnf(c_0_161,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_156]),c_0_34]),c_0_33])]),c_0_35])).

cnf(c_0_162,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_157,c_0_33])).

cnf(c_0_163,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v1_tex_2(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ v1_zfmisc_1(u1_struct_0(X1))
    | ~ r2_hidden(esk1_1(u1_struct_0(X1)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_158]),c_0_34])])).

cnf(c_0_164,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = u1_struct_0(esk4_0)
    | v2_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_78]),c_0_79])])).

cnf(c_0_165,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[c_0_160,c_0_161])).

cnf(c_0_166,negated_conjecture,
    ( esk1_1(u1_struct_0(esk4_0)) = esk5_0 ),
    inference(sr,[status(thm)],[c_0_101,c_0_161])).

cnf(c_0_167,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_162,c_0_161])).

cnf(c_0_168,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_164]),c_0_165]),c_0_41]),c_0_91]),c_0_166]),c_0_167])]),c_0_161])).

cnf(c_0_169,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_168]),c_0_34]),c_0_33])]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:20:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.70/0.85  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.70/0.85  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.70/0.85  #
% 0.70/0.85  # Preprocessing time       : 0.028 s
% 0.70/0.85  # Presaturation interreduction done
% 0.70/0.85  
% 0.70/0.85  # Proof found!
% 0.70/0.85  # SZS status Theorem
% 0.70/0.85  # SZS output start CNFRefutation
% 0.70/0.85  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 0.70/0.85  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.70/0.85  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.70/0.85  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.70/0.85  fof(t7_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 0.70/0.85  fof(cc1_zfmisc_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 0.70/0.85  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 0.70/0.85  fof(t8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~((v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))&v7_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 0.70/0.85  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.70/0.85  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.70/0.85  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.70/0.85  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.70/0.85  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.70/0.85  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.70/0.85  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.70/0.85  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.70/0.85  fof(t6_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 0.70/0.85  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.70/0.85  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.70/0.85  fof(fc14_subset_1, axiom, ![X1]:~(v1_subset_1(k2_subset_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 0.70/0.85  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.70/0.85  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.70/0.85  fof(c_0_22, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.70/0.85  fof(c_0_23, plain, ![X17, X18]:(((~m1_subset_1(X18,X17)|r2_hidden(X18,X17)|v1_xboole_0(X17))&(~r2_hidden(X18,X17)|m1_subset_1(X18,X17)|v1_xboole_0(X17)))&((~m1_subset_1(X18,X17)|v1_xboole_0(X18)|~v1_xboole_0(X17))&(~v1_xboole_0(X18)|m1_subset_1(X18,X17)|~v1_xboole_0(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.70/0.85  fof(c_0_24, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.70/0.85  fof(c_0_25, plain, ![X41, X42]:(((~v2_struct_0(k1_tex_2(X41,X42))|(v2_struct_0(X41)|~l1_pre_topc(X41)|~m1_subset_1(X42,u1_struct_0(X41))))&(v1_pre_topc(k1_tex_2(X41,X42))|(v2_struct_0(X41)|~l1_pre_topc(X41)|~m1_subset_1(X42,u1_struct_0(X41)))))&(m1_pre_topc(k1_tex_2(X41,X42),X41)|(v2_struct_0(X41)|~l1_pre_topc(X41)|~m1_subset_1(X42,u1_struct_0(X41))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.70/0.85  fof(c_0_26, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&((~v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)))&(v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.70/0.85  fof(c_0_27, plain, ![X47, X48]:(v1_xboole_0(X47)|v1_zfmisc_1(X47)|(~m1_subset_1(X48,X47)|v1_subset_1(k6_domain_1(X47,X48),X47))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).
% 0.70/0.85  fof(c_0_28, plain, ![X16]:(~v1_xboole_0(X16)|v1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).
% 0.70/0.85  cnf(c_0_29, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.70/0.85  cnf(c_0_30, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.85  fof(c_0_31, plain, ![X35, X36, X37]:((~v1_tex_2(X36,X35)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|(X37!=u1_struct_0(X36)|v1_subset_1(X37,u1_struct_0(X35))))|~m1_pre_topc(X36,X35)|~l1_pre_topc(X35))&((m1_subset_1(esk3_2(X35,X36),k1_zfmisc_1(u1_struct_0(X35)))|v1_tex_2(X36,X35)|~m1_pre_topc(X36,X35)|~l1_pre_topc(X35))&((esk3_2(X35,X36)=u1_struct_0(X36)|v1_tex_2(X36,X35)|~m1_pre_topc(X36,X35)|~l1_pre_topc(X35))&(~v1_subset_1(esk3_2(X35,X36),u1_struct_0(X35))|v1_tex_2(X36,X35)|~m1_pre_topc(X36,X35)|~l1_pre_topc(X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.70/0.85  cnf(c_0_32, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.70/0.85  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.70/0.85  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.70/0.85  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.70/0.85  cnf(c_0_36, plain, (v1_xboole_0(X1)|v1_zfmisc_1(X1)|v1_subset_1(k6_domain_1(X1,X2),X1)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.70/0.85  cnf(c_0_37, plain, (v1_zfmisc_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.70/0.85  cnf(c_0_38, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_29, c_0_30])).
% 0.70/0.85  cnf(c_0_39, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.85  cnf(c_0_40, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.70/0.85  cnf(c_0_41, negated_conjecture, (m1_pre_topc(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])]), c_0_35])).
% 0.70/0.85  cnf(c_0_42, plain, (esk3_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.70/0.85  fof(c_0_43, plain, ![X49, X50]:(v2_struct_0(X49)|~l1_struct_0(X49)|(~m1_subset_1(X50,u1_struct_0(X49))|(~v1_subset_1(k6_domain_1(u1_struct_0(X49),X50),u1_struct_0(X49))|~v7_struct_0(X49)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).
% 0.70/0.85  cnf(c_0_44, plain, (v1_subset_1(k6_domain_1(X1,X2),X1)|v1_zfmisc_1(X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[c_0_36, c_0_37])).
% 0.70/0.85  cnf(c_0_45, plain, (m1_subset_1(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.70/0.85  fof(c_0_46, plain, ![X39, X40]:((~v1_subset_1(X40,X39)|X40!=X39|~m1_subset_1(X40,k1_zfmisc_1(X39)))&(X40=X39|v1_subset_1(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.70/0.85  cnf(c_0_47, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|m1_subset_1(esk3_2(esk4_0,k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_34])])).
% 0.70/0.85  cnf(c_0_48, negated_conjecture, (esk3_2(esk4_0,k1_tex_2(esk4_0,esk5_0))=u1_struct_0(k1_tex_2(esk4_0,esk5_0))|v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_41]), c_0_34])])).
% 0.70/0.85  cnf(c_0_49, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.70/0.85  cnf(c_0_50, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~v7_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.70/0.85  cnf(c_0_51, plain, (v1_subset_1(k6_domain_1(X1,esk1_1(X1)),X1)|v1_zfmisc_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_37])).
% 0.70/0.85  cnf(c_0_52, negated_conjecture, (~v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.70/0.85  cnf(c_0_53, negated_conjecture, (v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))|v1_zfmisc_1(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_33])).
% 0.70/0.85  cnf(c_0_54, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.70/0.85  cnf(c_0_55, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|m1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.70/0.85  cnf(c_0_56, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|~v1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_48]), c_0_41]), c_0_34])])).
% 0.70/0.85  fof(c_0_57, plain, ![X43, X44]:(((~v2_struct_0(k1_tex_2(X43,X44))|(v2_struct_0(X43)|~l1_pre_topc(X43)|~m1_subset_1(X44,u1_struct_0(X43))))&(v7_struct_0(k1_tex_2(X43,X44))|(v2_struct_0(X43)|~l1_pre_topc(X43)|~m1_subset_1(X44,u1_struct_0(X43)))))&(v1_pre_topc(k1_tex_2(X43,X44))|(v2_struct_0(X43)|~l1_pre_topc(X43)|~m1_subset_1(X44,u1_struct_0(X43))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.70/0.85  fof(c_0_58, plain, ![X29, X30]:(v1_xboole_0(X29)|~m1_subset_1(X30,X29)|m1_subset_1(k6_domain_1(X29,X30),k1_zfmisc_1(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.70/0.85  cnf(c_0_59, plain, (v2_struct_0(X1)|v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(esk1_1(u1_struct_0(X1)),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.70/0.85  cnf(c_0_60, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk4_0))|~v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.70/0.85  cnf(c_0_61, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.70/0.85  cnf(c_0_62, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.70/0.85  fof(c_0_63, plain, ![X26, X27]:(~l1_pre_topc(X26)|(~m1_pre_topc(X27,X26)|l1_pre_topc(X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.70/0.85  fof(c_0_64, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|X10=X8|X9!=k1_tarski(X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_tarski(X8)))&((~r2_hidden(esk2_2(X12,X13),X13)|esk2_2(X12,X13)!=X12|X13=k1_tarski(X12))&(r2_hidden(esk2_2(X12,X13),X13)|esk2_2(X12,X13)=X12|X13=k1_tarski(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.70/0.85  fof(c_0_65, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.70/0.85  cnf(c_0_66, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.70/0.85  cnf(c_0_67, plain, (v2_struct_0(X1)|v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_45]), c_0_37])).
% 0.70/0.85  cnf(c_0_68, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_zfmisc_1(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.70/0.85  cnf(c_0_69, negated_conjecture, (v7_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_33]), c_0_34])]), c_0_35])).
% 0.70/0.85  fof(c_0_70, plain, ![X25]:(~l1_pre_topc(X25)|l1_struct_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.70/0.85  cnf(c_0_71, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.70/0.85  cnf(c_0_72, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.70/0.85  cnf(c_0_73, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.70/0.85  fof(c_0_74, plain, ![X31, X32]:(v1_xboole_0(X31)|~m1_subset_1(X32,X31)|k6_domain_1(X31,X32)=k1_tarski(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.70/0.85  fof(c_0_75, plain, ![X45, X46]:(v1_xboole_0(X45)|(~m1_subset_1(X46,X45)|(~v1_subset_1(k6_domain_1(X45,X46),X45)|~v1_zfmisc_1(X45)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).
% 0.70/0.85  cnf(c_0_76, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_66, c_0_33])).
% 0.70/0.85  cnf(c_0_77, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))|v1_zfmisc_1(u1_struct_0(esk4_0))|~l1_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])])).
% 0.70/0.85  cnf(c_0_78, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.70/0.85  cnf(c_0_79, negated_conjecture, (l1_pre_topc(k1_tex_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_41]), c_0_34])])).
% 0.70/0.85  cnf(c_0_80, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.70/0.85  cnf(c_0_81, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.70/0.85  cnf(c_0_82, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.70/0.85  cnf(c_0_83, plain, (v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~v1_subset_1(k6_domain_1(X1,X2),X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.70/0.85  cnf(c_0_84, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=u1_struct_0(esk4_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_76])).
% 0.70/0.85  cnf(c_0_85, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.70/0.85  cnf(c_0_86, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))|v1_zfmisc_1(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.70/0.85  cnf(c_0_87, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_80, c_0_73])).
% 0.70/0.85  cnf(c_0_88, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_81])])).
% 0.70/0.85  cnf(c_0_89, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_82, c_0_73])).
% 0.70/0.85  cnf(c_0_90, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=u1_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))|~v1_zfmisc_1(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_33])])).
% 0.70/0.85  cnf(c_0_91, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_34]), c_0_33])]), c_0_35])).
% 0.70/0.85  cnf(c_0_92, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_87])).
% 0.70/0.85  cnf(c_0_93, plain, (~v1_xboole_0(k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_30, c_0_88])).
% 0.70/0.85  cnf(c_0_94, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=k2_tarski(esk5_0,esk5_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_89, c_0_33])).
% 0.70/0.85  cnf(c_0_95, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=u1_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])])).
% 0.70/0.85  fof(c_0_96, plain, ![X28]:(v2_struct_0(X28)|~l1_struct_0(X28)|~v1_xboole_0(u1_struct_0(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.70/0.85  cnf(c_0_97, plain, (esk1_1(k2_tarski(X1,X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_39]), c_0_93])).
% 0.70/0.85  cnf(c_0_98, negated_conjecture, (k2_tarski(esk5_0,esk5_0)=u1_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.70/0.85  cnf(c_0_99, plain, (k2_tarski(esk1_1(X1),esk1_1(X1))=k6_domain_1(X1,esk1_1(X1))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_89, c_0_45])).
% 0.70/0.85  cnf(c_0_100, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.70/0.85  cnf(c_0_101, negated_conjecture, (esk1_1(u1_struct_0(esk4_0))=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.70/0.85  cnf(c_0_102, plain, (X1=esk1_1(X2)|v1_xboole_0(X2)|~r2_hidden(X1,k6_domain_1(X2,esk1_1(X2)))), inference(spm,[status(thm)],[c_0_92, c_0_99])).
% 0.70/0.85  cnf(c_0_103, negated_conjecture, (esk1_1(u1_struct_0(esk4_0))=esk5_0|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_35])).
% 0.70/0.85  cnf(c_0_104, negated_conjecture, (X1=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.70/0.85  cnf(c_0_105, plain, (v1_xboole_0(X1)|~v1_xboole_0(k6_domain_1(X1,esk1_1(X1)))), inference(spm,[status(thm)],[c_0_93, c_0_99])).
% 0.70/0.85  cnf(c_0_106, negated_conjecture, (X1=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_78]), c_0_34])])).
% 0.70/0.85  cnf(c_0_107, plain, (r2_hidden(esk1_1(X1),k6_domain_1(X1,esk1_1(X1)))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_88, c_0_99])).
% 0.70/0.85  cnf(c_0_108, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)|~v1_xboole_0(k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_105, c_0_103])).
% 0.70/0.85  cnf(c_0_109, negated_conjecture, (esk1_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0))=esk5_0|v1_xboole_0(k6_domain_1(u1_struct_0(esk4_0),esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_106, c_0_39])).
% 0.70/0.85  cnf(c_0_110, negated_conjecture, (r2_hidden(esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_107, c_0_103])).
% 0.70/0.85  cnf(c_0_111, negated_conjecture, (esk1_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0))=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.70/0.85  cnf(c_0_112, negated_conjecture, (r2_hidden(esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_78]), c_0_34])])).
% 0.70/0.85  cnf(c_0_113, plain, (m1_subset_1(k6_domain_1(X1,esk1_1(X1)),k1_zfmisc_1(X1))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_66, c_0_45])).
% 0.70/0.85  cnf(c_0_114, negated_conjecture, (esk1_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0))=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_78]), c_0_34])])).
% 0.70/0.85  cnf(c_0_115, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_112])).
% 0.70/0.85  cnf(c_0_116, negated_conjecture, (m1_subset_1(k6_domain_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk5_0),k1_zfmisc_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])).
% 0.70/0.85  cnf(c_0_117, negated_conjecture, (k6_domain_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk5_0)=k2_tarski(esk5_0,esk5_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_114]), c_0_115])).
% 0.70/0.85  fof(c_0_118, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|(~r2_hidden(X23,X22)|r2_hidden(X23,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.70/0.85  cnf(c_0_119, negated_conjecture, (m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 0.70/0.85  cnf(c_0_120, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_118])).
% 0.70/0.85  cnf(c_0_121, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_119, c_0_98])).
% 0.70/0.85  cnf(c_0_122, negated_conjecture, (r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_30])).
% 0.70/0.85  fof(c_0_123, plain, ![X24]:~v1_subset_1(k2_subset_1(X24),X24), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).
% 0.70/0.85  fof(c_0_124, plain, ![X19]:k2_subset_1(X19)=X19, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.70/0.85  cnf(c_0_125, negated_conjecture, (r2_hidden(X1,k2_tarski(esk5_0,esk5_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_94]), c_0_30])).
% 0.70/0.85  cnf(c_0_126, plain, (m1_subset_1(X1,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_38, c_0_88])).
% 0.70/0.85  cnf(c_0_127, plain, (~v1_subset_1(k2_subset_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 0.70/0.85  cnf(c_0_128, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_124])).
% 0.70/0.85  cnf(c_0_129, negated_conjecture, (m1_subset_1(X1,k2_tarski(esk5_0,esk5_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_125])).
% 0.70/0.85  cnf(c_0_130, plain, (k6_domain_1(k2_tarski(X1,X1),X1)=k2_tarski(X1,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_126]), c_0_93])).
% 0.70/0.85  cnf(c_0_131, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_127, c_0_128])).
% 0.70/0.85  cnf(c_0_132, negated_conjecture, (k6_domain_1(k2_tarski(esk5_0,esk5_0),X1)=k2_tarski(X1,X1)|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_129]), c_0_93])).
% 0.70/0.85  cnf(c_0_133, plain, (v1_zfmisc_1(k2_tarski(X1,X1))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_97]), c_0_130]), c_0_131])).
% 0.70/0.85  cnf(c_0_134, negated_conjecture, (~v1_subset_1(k2_tarski(X1,X1),k2_tarski(esk5_0,esk5_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_132]), c_0_133])]), c_0_93]), c_0_129])).
% 0.70/0.85  fof(c_0_135, plain, ![X33, X34]:(~l1_pre_topc(X33)|(~m1_pre_topc(X34,X33)|m1_subset_1(u1_struct_0(X34),k1_zfmisc_1(u1_struct_0(X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.70/0.85  cnf(c_0_136, negated_conjecture, (~v1_subset_1(k2_tarski(X1,X1),u1_struct_0(esk4_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_98]), c_0_30])).
% 0.70/0.85  cnf(c_0_137, plain, (k6_domain_1(X1,esk1_1(X1))=X1|v1_subset_1(k6_domain_1(X1,esk1_1(X1)),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_54, c_0_113])).
% 0.70/0.85  cnf(c_0_138, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_135])).
% 0.70/0.85  cnf(c_0_139, negated_conjecture, (v1_xboole_0(X1)|~v1_subset_1(k6_domain_1(X1,esk1_1(X1)),u1_struct_0(esk4_0))|~r2_hidden(esk1_1(X1),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_136, c_0_99])).
% 0.70/0.85  cnf(c_0_140, plain, (k6_domain_1(X1,esk1_1(X1))=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_137]), c_0_45])).
% 0.70/0.85  cnf(c_0_141, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_54, c_0_138])).
% 0.70/0.85  cnf(c_0_142, plain, (r2_hidden(X1,u1_struct_0(X2))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_struct_0(X3))), inference(spm,[status(thm)],[c_0_120, c_0_138])).
% 0.70/0.85  cnf(c_0_143, negated_conjecture, (v1_xboole_0(X1)|~v1_subset_1(X1,u1_struct_0(esk4_0))|~v1_zfmisc_1(X1)|~r2_hidden(esk1_1(X1),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 0.70/0.85  cnf(c_0_144, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_subset_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_41]), c_0_34])])).
% 0.70/0.85  cnf(c_0_145, plain, (r2_hidden(esk1_1(u1_struct_0(X1)),u1_struct_0(X2))|v1_xboole_0(u1_struct_0(X1))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_142, c_0_39])).
% 0.70/0.85  cnf(c_0_146, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))|~v1_zfmisc_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))|~r2_hidden(esk1_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0))),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_143, c_0_144])).
% 0.70/0.85  cnf(c_0_147, negated_conjecture, (r2_hidden(esk1_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0))),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_41]), c_0_34])])).
% 0.70/0.85  cnf(c_0_148, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v2_struct_0(k1_tex_2(esk4_0,esk5_0))|~l1_struct_0(k1_tex_2(esk4_0,esk5_0))|~r2_hidden(esk1_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0))),u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_67]), c_0_69])]), c_0_100])).
% 0.70/0.85  cnf(c_0_149, negated_conjecture, (v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_147])).
% 0.70/0.85  cnf(c_0_150, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v2_struct_0(k1_tex_2(esk4_0,esk5_0))|~r2_hidden(esk1_1(u1_struct_0(k1_tex_2(esk4_0,esk5_0))),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_78]), c_0_79])])).
% 0.70/0.85  cnf(c_0_151, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.70/0.85  cnf(c_0_152, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))|~l1_struct_0(k1_tex_2(esk4_0,esk5_0))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_100, c_0_149])).
% 0.70/0.85  cnf(c_0_153, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.70/0.85  cnf(c_0_154, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v2_struct_0(k1_tex_2(esk4_0,esk5_0))|v1_xboole_0(u1_struct_0(k1_tex_2(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_150, c_0_147])).
% 0.70/0.85  cnf(c_0_155, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))|~v1_zfmisc_1(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_151]), c_0_33])])).
% 0.70/0.85  cnf(c_0_156, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_78]), c_0_79])])).
% 0.70/0.85  cnf(c_0_157, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.70/0.85  cnf(c_0_158, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_153]), c_0_138])).
% 0.70/0.85  cnf(c_0_159, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v2_struct_0(k1_tex_2(esk4_0,esk5_0))|~l1_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_100, c_0_154])).
% 0.70/0.85  cnf(c_0_160, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_155, c_0_91])])).
% 0.70/0.85  cnf(c_0_161, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_156]), c_0_34]), c_0_33])]), c_0_35])).
% 0.70/0.85  cnf(c_0_162, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_157, c_0_33])).
% 0.70/0.85  cnf(c_0_163, negated_conjecture, (v1_xboole_0(u1_struct_0(X1))|~v1_tex_2(X1,esk4_0)|~m1_pre_topc(X1,esk4_0)|~v1_zfmisc_1(u1_struct_0(X1))|~r2_hidden(esk1_1(u1_struct_0(X1)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_158]), c_0_34])])).
% 0.70/0.85  cnf(c_0_164, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=u1_struct_0(esk4_0)|v2_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_78]), c_0_79])])).
% 0.70/0.85  cnf(c_0_165, negated_conjecture, (v1_tex_2(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[c_0_160, c_0_161])).
% 0.70/0.85  cnf(c_0_166, negated_conjecture, (esk1_1(u1_struct_0(esk4_0))=esk5_0), inference(sr,[status(thm)],[c_0_101, c_0_161])).
% 0.70/0.85  cnf(c_0_167, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[c_0_162, c_0_161])).
% 0.70/0.85  cnf(c_0_168, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_164]), c_0_165]), c_0_41]), c_0_91]), c_0_166]), c_0_167])]), c_0_161])).
% 0.70/0.85  cnf(c_0_169, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_168]), c_0_34]), c_0_33])]), c_0_35]), ['proof']).
% 0.70/0.85  # SZS output end CNFRefutation
% 0.70/0.85  # Proof object total steps             : 170
% 0.70/0.85  # Proof object clause steps            : 125
% 0.70/0.85  # Proof object formula steps           : 45
% 0.70/0.85  # Proof object conjectures             : 72
% 0.70/0.85  # Proof object clause conjectures      : 69
% 0.70/0.85  # Proof object formula conjectures     : 3
% 0.70/0.85  # Proof object initial clauses used    : 33
% 0.70/0.85  # Proof object initial formulas used   : 22
% 0.70/0.85  # Proof object generating inferences   : 78
% 0.70/0.85  # Proof object simplifying inferences  : 100
% 0.70/0.85  # Training examples: 0 positive, 0 negative
% 0.70/0.85  # Parsed axioms                        : 23
% 0.70/0.85  # Removed by relevancy pruning/SinE    : 0
% 0.70/0.85  # Initial clauses                      : 42
% 0.70/0.85  # Removed in clause preprocessing      : 2
% 0.70/0.85  # Initial clauses in saturation        : 40
% 0.70/0.85  # Processed clauses                    : 2018
% 0.70/0.85  # ...of these trivial                  : 66
% 0.70/0.85  # ...subsumed                          : 1283
% 0.70/0.85  # ...remaining for further processing  : 669
% 0.70/0.85  # Other redundant clauses eliminated   : 32
% 0.70/0.85  # Clauses deleted for lack of memory   : 0
% 0.70/0.85  # Backward-subsumed                    : 61
% 0.70/0.85  # Backward-rewritten                   : 175
% 0.70/0.85  # Generated clauses                    : 17986
% 0.70/0.85  # ...of the previous two non-trivial   : 17103
% 0.70/0.85  # Contextual simplify-reflections      : 127
% 0.70/0.85  # Paramodulations                      : 17843
% 0.70/0.85  # Factorizations                       : 17
% 0.70/0.85  # Equation resolutions                 : 32
% 0.70/0.85  # Propositional unsat checks           : 0
% 0.70/0.85  #    Propositional check models        : 0
% 0.70/0.85  #    Propositional check unsatisfiable : 0
% 0.70/0.85  #    Propositional clauses             : 0
% 0.70/0.85  #    Propositional clauses after purity: 0
% 0.70/0.85  #    Propositional unsat core size     : 0
% 0.70/0.85  #    Propositional preprocessing time  : 0.000
% 0.70/0.85  #    Propositional encoding time       : 0.000
% 0.70/0.85  #    Propositional solver time         : 0.000
% 0.70/0.85  #    Success case prop preproc time    : 0.000
% 0.70/0.85  #    Success case prop encoding time   : 0.000
% 0.70/0.85  #    Success case prop solver time     : 0.000
% 0.70/0.85  # Current number of processed clauses  : 297
% 0.70/0.85  #    Positive orientable unit clauses  : 24
% 0.70/0.85  #    Positive unorientable unit clauses: 0
% 0.70/0.85  #    Negative unit clauses             : 9
% 0.70/0.85  #    Non-unit-clauses                  : 264
% 0.70/0.85  # Current number of unprocessed clauses: 15092
% 0.70/0.85  # ...number of literals in the above   : 85178
% 0.70/0.85  # Current number of archived formulas  : 0
% 0.70/0.85  # Current number of archived clauses   : 370
% 0.70/0.85  # Clause-clause subsumption calls (NU) : 50942
% 0.70/0.85  # Rec. Clause-clause subsumption calls : 26352
% 0.70/0.85  # Non-unit clause-clause subsumptions  : 1157
% 0.70/0.85  # Unit Clause-clause subsumption calls : 428
% 0.70/0.85  # Rewrite failures with RHS unbound    : 0
% 0.70/0.85  # BW rewrite match attempts            : 13
% 0.70/0.85  # BW rewrite match successes           : 11
% 0.70/0.85  # Condensation attempts                : 0
% 0.70/0.85  # Condensation successes               : 0
% 0.70/0.85  # Termbank termtop insertions          : 359149
% 0.70/0.85  
% 0.70/0.85  # -------------------------------------------------
% 0.70/0.85  # User time                : 0.499 s
% 0.70/0.85  # System time              : 0.012 s
% 0.70/0.85  # Total time               : 0.511 s
% 0.70/0.85  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
