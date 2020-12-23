%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:31 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 842 expanded)
%              Number of clauses        :   79 ( 364 expanded)
%              Number of leaves         :   22 ( 208 expanded)
%              Depth                    :   26
%              Number of atoms          :  443 (3272 expanded)
%              Number of equality atoms :   43 ( 190 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc5_funct_1,axiom,(
    ! [X1] :
      ( v1_zfmisc_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_zfmisc_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(rc1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
          & ~ v1_xboole_0(X2)
          & v1_zfmisc_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_tex_2)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(rc1_connsp_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).

fof(t20_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v1_tex_2(k1_tex_2(X1,X2),X1)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(t13_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v1_subset_1(X3,u1_struct_0(X1))
                <=> v1_tex_2(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

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

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

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

fof(cc2_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_xboole_0(X2)
           => ~ v1_subset_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t6_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(c_0_22,plain,(
    ! [X28,X29] :
      ( ~ v1_zfmisc_1(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | v1_zfmisc_1(X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc5_funct_1])])])).

fof(c_0_23,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_24,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_25,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_26,plain,
    ( v1_zfmisc_1(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_32,plain,(
    ! [X47] :
      ( ( m1_subset_1(esk5_1(X47),k1_zfmisc_1(X47))
        | v1_xboole_0(X47) )
      & ( ~ v1_xboole_0(esk5_1(X47))
        | v1_xboole_0(X47) )
      & ( v1_zfmisc_1(esk5_1(X47))
        | v1_xboole_0(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_tex_2])])])])])).

fof(c_0_33,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X18,X17)
        | X18 = X15
        | X18 = X16
        | X17 != k2_tarski(X15,X16) )
      & ( X19 != X15
        | r2_hidden(X19,X17)
        | X17 != k2_tarski(X15,X16) )
      & ( X19 != X16
        | r2_hidden(X19,X17)
        | X17 != k2_tarski(X15,X16) )
      & ( esk3_3(X20,X21,X22) != X20
        | ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k2_tarski(X20,X21) )
      & ( esk3_3(X20,X21,X22) != X21
        | ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k2_tarski(X20,X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X22)
        | esk3_3(X20,X21,X22) = X20
        | esk3_3(X20,X21,X22) = X21
        | X22 = k2_tarski(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_34,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_zfmisc_1(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( v1_zfmisc_1(esk5_1(X1))
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_36,plain,(
    ! [X35] :
      ( ( m1_subset_1(esk4_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_pre_topc(X35) )
      & ( v1_xboole_0(esk4_1(X35))
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc1_connsp_1])])])])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_38,plain,(
    ! [X49,X50,X51] :
      ( ( ~ v1_subset_1(X51,u1_struct_0(X49))
        | v1_tex_2(X50,X49)
        | X51 != u1_struct_0(X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ m1_pre_topc(X50,X49)
        | ~ l1_pre_topc(X49) )
      & ( ~ v1_tex_2(X50,X49)
        | v1_subset_1(X51,u1_struct_0(X49))
        | X51 != u1_struct_0(X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ m1_pre_topc(X50,X49)
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_tex_2])])])])).

fof(c_0_39,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_pre_topc(X38,X37)
      | m1_subset_1(u1_struct_0(X38),k1_zfmisc_1(u1_struct_0(X37))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_40,plain,(
    ! [X41,X42] :
      ( ( ~ v1_subset_1(X42,X41)
        | X42 != X41
        | ~ m1_subset_1(X42,k1_zfmisc_1(X41)) )
      & ( X42 = X41
        | v1_subset_1(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(X41)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( v1_zfmisc_1(X1)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( v1_xboole_0(esk4_1(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & l1_pre_topc(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & ( ~ v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),u1_struct_0(esk6_0)) )
    & ( v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),u1_struct_0(esk6_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_37])])])])).

cnf(c_0_45,plain,
    ( v1_tex_2(X3,X2)
    | ~ v1_subset_1(X1,u1_struct_0(X2))
    | X1 != u1_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).

cnf(c_0_49,plain,
    ( v1_zfmisc_1(esk4_1(X1))
    | v1_xboole_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_51,plain,(
    ! [X54,X55] :
      ( v1_xboole_0(X54)
      | v1_zfmisc_1(X54)
      | ~ m1_subset_1(X55,X54)
      | v1_subset_1(k6_domain_1(X54,X55),X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).

cnf(c_0_52,plain,
    ( v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_46])).

cnf(c_0_53,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

fof(c_0_54,plain,(
    ! [X43,X44] :
      ( ( ~ v2_struct_0(k1_tex_2(X43,X44))
        | v2_struct_0(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43)) )
      & ( v1_pre_topc(k1_tex_2(X43,X44))
        | v2_struct_0(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43)) )
      & ( m1_pre_topc(k1_tex_2(X43,X44),X43)
        | v2_struct_0(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

cnf(c_0_55,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( v1_zfmisc_1(esk4_1(esk6_0))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_60,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( v1_zfmisc_1(esk4_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_63,plain,(
    ! [X56,X57] :
      ( v2_struct_0(X56)
      | ~ l1_struct_0(X56)
      | ~ m1_subset_1(X57,u1_struct_0(X56))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X56),X57),u1_struct_0(X56))
      | ~ v7_struct_0(X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

fof(c_0_64,plain,(
    ! [X34] :
      ( v2_struct_0(X34)
      | ~ l1_struct_0(X34)
      | ~ v1_xboole_0(u1_struct_0(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_65,plain,(
    ! [X33] :
      ( ~ v2_struct_0(X33)
      | ~ l1_struct_0(X33)
      | v1_xboole_0(u1_struct_0(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

cnf(c_0_66,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk6_0))
    | v1_xboole_0(u1_struct_0(esk6_0))
    | ~ v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_67,plain,
    ( u1_struct_0(k1_tex_2(X1,X2)) = u1_struct_0(X1)
    | v1_tex_2(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_69,negated_conjecture,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_62])).

fof(c_0_70,plain,(
    ! [X24,X25] :
      ( ~ v1_xboole_0(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | ~ v1_subset_1(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk6_0,esk7_0)) = u1_struct_0(esk6_0)
    | v1_zfmisc_1(u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_50]),c_0_59])]),c_0_68]),c_0_69])).

cnf(c_0_75,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_58]),c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk6_0))
    | ~ v2_struct_0(k1_tex_2(esk6_0,esk7_0))
    | ~ l1_struct_0(k1_tex_2(esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_69])).

fof(c_0_78,plain,(
    ! [X45,X46] :
      ( ( ~ v2_struct_0(k1_tex_2(X45,X46))
        | v2_struct_0(X45)
        | ~ l1_pre_topc(X45)
        | ~ m1_subset_1(X46,u1_struct_0(X45)) )
      & ( v7_struct_0(k1_tex_2(X45,X46))
        | v2_struct_0(X45)
        | ~ l1_pre_topc(X45)
        | ~ m1_subset_1(X46,u1_struct_0(X45)) )
      & ( v1_pre_topc(k1_tex_2(X45,X46))
        | v2_struct_0(X45)
        | ~ l1_pre_topc(X45)
        | ~ m1_subset_1(X46,u1_struct_0(X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_79,plain,
    ( ~ v1_subset_1(X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_27])).

cnf(c_0_80,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_27])).

fof(c_0_81,plain,(
    ! [X39,X40] :
      ( v1_xboole_0(X39)
      | ~ v1_zfmisc_1(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | v1_xboole_0(X40)
      | ~ v1_subset_1(X40,X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).

cnf(c_0_82,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk6_0))
    | ~ v7_struct_0(k1_tex_2(esk6_0,esk7_0))
    | ~ l1_struct_0(k1_tex_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_74]),c_0_77])).

cnf(c_0_83,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

fof(c_0_84,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_85,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X31)
      | l1_pre_topc(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_86,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_87,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk6_0))
    | ~ l1_struct_0(k1_tex_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_50]),c_0_59])]),c_0_68])).

cnf(c_0_89,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_90,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_91,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_31])).

cnf(c_0_92,plain,
    ( v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X2)
    | ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[c_0_87,c_0_75])).

cnf(c_0_93,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_94,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk6_0))
    | ~ l1_pre_topc(k1_tex_2(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_61])).

cnf(c_0_96,plain,
    ( X1 = esk4_1(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_43])).

cnf(c_0_97,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_zfmisc_1(u1_struct_0(X2))
    | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_46])).

cnf(c_0_98,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_93]),c_0_46])).

cnf(c_0_99,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_50]),c_0_59])]),c_0_68])).

cnf(c_0_100,negated_conjecture,
    ( X1 = esk4_1(esk6_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_50])).

cnf(c_0_101,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_zfmisc_1(u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_59])).

fof(c_0_103,plain,(
    ! [X52,X53] :
      ( v1_xboole_0(X52)
      | ~ m1_subset_1(X53,X52)
      | ~ v1_subset_1(k6_domain_1(X52,X53),X52)
      | ~ v1_zfmisc_1(X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).

cnf(c_0_104,negated_conjecture,
    ( esk4_1(X1) = esk4_1(esk6_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_100,c_0_43])).

cnf(c_0_105,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v1_tex_2(X1,esk6_0)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_50])])).

cnf(c_0_106,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_108,negated_conjecture,
    ( esk4_1(k1_tex_2(X1,X2)) = esk4_1(esk6_0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_95])).

cnf(c_0_109,negated_conjecture,
    ( u1_struct_0(X1) = esk4_1(esk6_0)
    | ~ v1_tex_2(X1,esk6_0)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk6_0))
    | ~ v1_zfmisc_1(u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_59])])).

cnf(c_0_111,negated_conjecture,
    ( esk4_1(k1_tex_2(esk6_0,esk7_0)) = esk4_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_59]),c_0_50])]),c_0_68])).

cnf(c_0_112,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk6_0,X1)) = esk4_1(esk6_0)
    | ~ v1_tex_2(k1_tex_2(esk6_0,X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_61]),c_0_50])]),c_0_68])).

cnf(c_0_113,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_102])])).

cnf(c_0_114,negated_conjecture,
    ( v1_xboole_0(esk4_1(esk6_0))
    | ~ l1_pre_topc(k1_tex_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk6_0,esk7_0)) = esk4_1(esk6_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_59])])).

cnf(c_0_116,negated_conjecture,
    ( v1_xboole_0(esk4_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_95]),c_0_50]),c_0_59])]),c_0_68])).

cnf(c_0_117,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_118,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk6_0,esk7_0))
    | v1_xboole_0(u1_struct_0(esk6_0))
    | ~ l1_struct_0(k1_tex_2(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_115]),c_0_116])])).

cnf(c_0_119,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | ~ l1_struct_0(k1_tex_2(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_50]),c_0_59])]),c_0_68])).

cnf(c_0_120,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | ~ l1_pre_topc(k1_tex_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_89])).

cnf(c_0_121,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_95]),c_0_50]),c_0_59])]),c_0_68])).

cnf(c_0_122,negated_conjecture,
    ( ~ l1_struct_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_121]),c_0_68])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_89]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.21/0.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.029 s
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(cc5_funct_1, axiom, ![X1]:(v1_zfmisc_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_1)).
% 0.21/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.42  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.42  fof(rc1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_xboole_0(X2)))&v1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_tex_2)).
% 0.21/0.42  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.21/0.42  fof(rc1_connsp_1, axiom, ![X1]:(l1_pre_topc(X1)=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_connsp_1)).
% 0.21/0.42  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 0.21/0.42  fof(t13_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v1_subset_1(X3,u1_struct_0(X1))<=>v1_tex_2(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tex_2)).
% 0.21/0.42  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.21/0.42  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.21/0.42  fof(t7_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 0.21/0.42  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.21/0.42  fof(t8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~((v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))&v7_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 0.21/0.42  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.21/0.42  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.21/0.42  fof(cc4_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~(v1_subset_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 0.21/0.42  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.21/0.42  fof(cc2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_xboole_0(X2))=>~(v1_subset_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 0.21/0.42  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.42  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.42  fof(t6_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.21/0.42  fof(c_0_22, plain, ![X28, X29]:(~v1_zfmisc_1(X28)|(~m1_subset_1(X29,k1_zfmisc_1(X28))|v1_zfmisc_1(X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc5_funct_1])])])).
% 0.21/0.42  fof(c_0_23, plain, ![X26, X27]:((~m1_subset_1(X26,k1_zfmisc_1(X27))|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|m1_subset_1(X26,k1_zfmisc_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.42  fof(c_0_24, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.42  fof(c_0_25, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.42  cnf(c_0_26, plain, (v1_zfmisc_1(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.42  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.42  cnf(c_0_28, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.42  cnf(c_0_29, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.42  cnf(c_0_30, plain, (v1_zfmisc_1(X1)|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.42  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.42  fof(c_0_32, plain, ![X47]:(((m1_subset_1(esk5_1(X47),k1_zfmisc_1(X47))|v1_xboole_0(X47))&(~v1_xboole_0(esk5_1(X47))|v1_xboole_0(X47)))&(v1_zfmisc_1(esk5_1(X47))|v1_xboole_0(X47))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_tex_2])])])])])).
% 0.21/0.42  fof(c_0_33, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X18,X17)|(X18=X15|X18=X16)|X17!=k2_tarski(X15,X16))&((X19!=X15|r2_hidden(X19,X17)|X17!=k2_tarski(X15,X16))&(X19!=X16|r2_hidden(X19,X17)|X17!=k2_tarski(X15,X16))))&(((esk3_3(X20,X21,X22)!=X20|~r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k2_tarski(X20,X21))&(esk3_3(X20,X21,X22)!=X21|~r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k2_tarski(X20,X21)))&(r2_hidden(esk3_3(X20,X21,X22),X22)|(esk3_3(X20,X21,X22)=X20|esk3_3(X20,X21,X22)=X21)|X22=k2_tarski(X20,X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.21/0.42  cnf(c_0_34, plain, (v1_zfmisc_1(X1)|~v1_zfmisc_1(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.42  cnf(c_0_35, plain, (v1_zfmisc_1(esk5_1(X1))|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.42  fof(c_0_36, plain, ![X35]:((m1_subset_1(esk4_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X35))&(v1_xboole_0(esk4_1(X35))|~l1_pre_topc(X35))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc1_connsp_1])])])])).
% 0.21/0.42  fof(c_0_37, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.21/0.42  fof(c_0_38, plain, ![X49, X50, X51]:((~v1_subset_1(X51,u1_struct_0(X49))|v1_tex_2(X50,X49)|X51!=u1_struct_0(X50)|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))|~m1_pre_topc(X50,X49)|~l1_pre_topc(X49))&(~v1_tex_2(X50,X49)|v1_subset_1(X51,u1_struct_0(X49))|X51!=u1_struct_0(X50)|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))|~m1_pre_topc(X50,X49)|~l1_pre_topc(X49))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_tex_2])])])])).
% 0.21/0.42  fof(c_0_39, plain, ![X37, X38]:(~l1_pre_topc(X37)|(~m1_pre_topc(X38,X37)|m1_subset_1(u1_struct_0(X38),k1_zfmisc_1(u1_struct_0(X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.21/0.42  fof(c_0_40, plain, ![X41, X42]:((~v1_subset_1(X42,X41)|X42!=X41|~m1_subset_1(X42,k1_zfmisc_1(X41)))&(X42=X41|v1_subset_1(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(X41)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.21/0.42  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.42  cnf(c_0_42, plain, (v1_zfmisc_1(X1)|v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.42  cnf(c_0_43, plain, (v1_xboole_0(esk4_1(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.42  fof(c_0_44, negated_conjecture, ((~v2_struct_0(esk6_0)&l1_pre_topc(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&((~v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),u1_struct_0(esk6_0)))&(v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),u1_struct_0(esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_37])])])])).
% 0.21/0.42  cnf(c_0_45, plain, (v1_tex_2(X3,X2)|~v1_subset_1(X1,u1_struct_0(X2))|X1!=u1_struct_0(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.42  cnf(c_0_46, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.42  cnf(c_0_47, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.42  cnf(c_0_48, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).
% 0.21/0.42  cnf(c_0_49, plain, (v1_zfmisc_1(esk4_1(X1))|v1_xboole_0(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.42  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.42  fof(c_0_51, plain, ![X54, X55]:(v1_xboole_0(X54)|v1_zfmisc_1(X54)|(~m1_subset_1(X55,X54)|v1_subset_1(k6_domain_1(X54,X55),X54))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_tex_2])])])])).
% 0.21/0.42  cnf(c_0_52, plain, (v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]), c_0_46])).
% 0.21/0.42  cnf(c_0_53, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 0.21/0.42  fof(c_0_54, plain, ![X43, X44]:(((~v2_struct_0(k1_tex_2(X43,X44))|(v2_struct_0(X43)|~l1_pre_topc(X43)|~m1_subset_1(X44,u1_struct_0(X43))))&(v1_pre_topc(k1_tex_2(X43,X44))|(v2_struct_0(X43)|~l1_pre_topc(X43)|~m1_subset_1(X44,u1_struct_0(X43)))))&(m1_pre_topc(k1_tex_2(X43,X44),X43)|(v2_struct_0(X43)|~l1_pre_topc(X43)|~m1_subset_1(X44,u1_struct_0(X43))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.21/0.42  cnf(c_0_55, plain, (~v1_xboole_0(k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_28, c_0_48])).
% 0.21/0.42  cnf(c_0_56, negated_conjecture, (v1_zfmisc_1(esk4_1(esk6_0))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.42  cnf(c_0_57, negated_conjecture, (~v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.42  cnf(c_0_58, plain, (v1_xboole_0(X1)|v1_zfmisc_1(X1)|v1_subset_1(k6_domain_1(X1,X2),X1)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.42  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.42  cnf(c_0_60, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.42  cnf(c_0_61, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.42  cnf(c_0_62, negated_conjecture, (v1_zfmisc_1(esk4_1(esk6_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.21/0.42  fof(c_0_63, plain, ![X56, X57]:(v2_struct_0(X56)|~l1_struct_0(X56)|(~m1_subset_1(X57,u1_struct_0(X56))|(~v1_subset_1(k6_domain_1(u1_struct_0(X56),X57),u1_struct_0(X56))|~v7_struct_0(X56)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).
% 0.21/0.42  fof(c_0_64, plain, ![X34]:(v2_struct_0(X34)|~l1_struct_0(X34)|~v1_xboole_0(u1_struct_0(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.21/0.42  fof(c_0_65, plain, ![X33]:(~v2_struct_0(X33)|~l1_struct_0(X33)|v1_xboole_0(u1_struct_0(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.21/0.42  cnf(c_0_66, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk6_0))|v1_xboole_0(u1_struct_0(esk6_0))|~v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.21/0.42  cnf(c_0_67, plain, (u1_struct_0(k1_tex_2(X1,X2))=u1_struct_0(X1)|v1_tex_2(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.42  cnf(c_0_68, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.42  cnf(c_0_69, negated_conjecture, (v1_zfmisc_1(X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_62])).
% 0.21/0.42  fof(c_0_70, plain, ![X24, X25]:(~v1_xboole_0(X24)|(~m1_subset_1(X25,k1_zfmisc_1(X24))|~v1_subset_1(X25,X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).
% 0.21/0.42  cnf(c_0_71, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~v7_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.42  cnf(c_0_72, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.42  cnf(c_0_73, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.42  cnf(c_0_74, negated_conjecture, (u1_struct_0(k1_tex_2(esk6_0,esk7_0))=u1_struct_0(esk6_0)|v1_zfmisc_1(u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_50]), c_0_59])]), c_0_68]), c_0_69])).
% 0.21/0.42  cnf(c_0_75, plain, (~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.21/0.42  cnf(c_0_76, plain, (v2_struct_0(X1)|v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_58]), c_0_72])).
% 0.21/0.42  cnf(c_0_77, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk6_0))|~v2_struct_0(k1_tex_2(esk6_0,esk7_0))|~l1_struct_0(k1_tex_2(esk6_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_69])).
% 0.21/0.42  fof(c_0_78, plain, ![X45, X46]:(((~v2_struct_0(k1_tex_2(X45,X46))|(v2_struct_0(X45)|~l1_pre_topc(X45)|~m1_subset_1(X46,u1_struct_0(X45))))&(v7_struct_0(k1_tex_2(X45,X46))|(v2_struct_0(X45)|~l1_pre_topc(X45)|~m1_subset_1(X46,u1_struct_0(X45)))))&(v1_pre_topc(k1_tex_2(X45,X46))|(v2_struct_0(X45)|~l1_pre_topc(X45)|~m1_subset_1(X46,u1_struct_0(X45))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.21/0.42  cnf(c_0_79, plain, (~v1_subset_1(X1,X2)|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_75, c_0_27])).
% 0.21/0.42  cnf(c_0_80, plain, (X1=X2|v1_subset_1(X1,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_27])).
% 0.21/0.42  fof(c_0_81, plain, ![X39, X40]:(v1_xboole_0(X39)|~v1_zfmisc_1(X39)|(~m1_subset_1(X40,k1_zfmisc_1(X39))|(v1_xboole_0(X40)|~v1_subset_1(X40,X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).
% 0.21/0.42  cnf(c_0_82, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk6_0))|~v7_struct_0(k1_tex_2(esk6_0,esk7_0))|~l1_struct_0(k1_tex_2(esk6_0,esk7_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_74]), c_0_77])).
% 0.21/0.42  cnf(c_0_83, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.21/0.42  fof(c_0_84, plain, ![X30]:(~l1_pre_topc(X30)|l1_struct_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.42  fof(c_0_85, plain, ![X31, X32]:(~l1_pre_topc(X31)|(~m1_pre_topc(X32,X31)|l1_pre_topc(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.42  cnf(c_0_86, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.21/0.42  cnf(c_0_87, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.21/0.42  cnf(c_0_88, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk6_0))|~l1_struct_0(k1_tex_2(esk6_0,esk7_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_50]), c_0_59])]), c_0_68])).
% 0.21/0.42  cnf(c_0_89, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.21/0.42  cnf(c_0_90, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.21/0.42  cnf(c_0_91, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_86, c_0_31])).
% 0.21/0.42  cnf(c_0_92, plain, (v1_xboole_0(X1)|~v1_zfmisc_1(X2)|~v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[c_0_87, c_0_75])).
% 0.21/0.42  cnf(c_0_93, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.42  cnf(c_0_94, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk6_0))|~l1_pre_topc(k1_tex_2(esk6_0,esk7_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.21/0.42  cnf(c_0_95, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_90, c_0_61])).
% 0.21/0.42  cnf(c_0_96, plain, (X1=esk4_1(X2)|~l1_pre_topc(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_91, c_0_43])).
% 0.21/0.42  cnf(c_0_97, plain, (v1_xboole_0(u1_struct_0(X1))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v1_zfmisc_1(u1_struct_0(X2))|~v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_92, c_0_46])).
% 0.21/0.42  cnf(c_0_98, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_93]), c_0_46])).
% 0.21/0.42  cnf(c_0_99, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_50]), c_0_59])]), c_0_68])).
% 0.21/0.42  cnf(c_0_100, negated_conjecture, (X1=esk4_1(esk6_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_96, c_0_50])).
% 0.21/0.42  cnf(c_0_101, plain, (v1_xboole_0(u1_struct_0(X1))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v1_zfmisc_1(u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.21/0.42  cnf(c_0_102, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_99, c_0_59])).
% 0.21/0.42  fof(c_0_103, plain, ![X52, X53]:(v1_xboole_0(X52)|(~m1_subset_1(X53,X52)|(~v1_subset_1(k6_domain_1(X52,X53),X52)|~v1_zfmisc_1(X52)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).
% 0.21/0.42  cnf(c_0_104, negated_conjecture, (esk4_1(X1)=esk4_1(esk6_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_100, c_0_43])).
% 0.21/0.42  cnf(c_0_105, negated_conjecture, (v1_xboole_0(u1_struct_0(X1))|~v1_tex_2(X1,esk6_0)|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_50])])).
% 0.21/0.42  cnf(c_0_106, plain, (v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~v1_subset_1(k6_domain_1(X1,X2),X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.21/0.42  cnf(c_0_107, negated_conjecture, (v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.42  cnf(c_0_108, negated_conjecture, (esk4_1(k1_tex_2(X1,X2))=esk4_1(esk6_0)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_104, c_0_95])).
% 0.21/0.42  cnf(c_0_109, negated_conjecture, (u1_struct_0(X1)=esk4_1(esk6_0)|~v1_tex_2(X1,esk6_0)|~m1_pre_topc(X1,esk6_0)), inference(spm,[status(thm)],[c_0_100, c_0_105])).
% 0.21/0.42  cnf(c_0_110, negated_conjecture, (v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)|v1_xboole_0(u1_struct_0(esk6_0))|~v1_zfmisc_1(u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_59])])).
% 0.21/0.42  cnf(c_0_111, negated_conjecture, (esk4_1(k1_tex_2(esk6_0,esk7_0))=esk4_1(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_59]), c_0_50])]), c_0_68])).
% 0.21/0.42  cnf(c_0_112, negated_conjecture, (u1_struct_0(k1_tex_2(esk6_0,X1))=esk4_1(esk6_0)|~v1_tex_2(k1_tex_2(esk6_0,X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_61]), c_0_50])]), c_0_68])).
% 0.21/0.42  cnf(c_0_113, negated_conjecture, (v1_tex_2(k1_tex_2(esk6_0,esk7_0),esk6_0)|v1_xboole_0(u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_102])])).
% 0.21/0.42  cnf(c_0_114, negated_conjecture, (v1_xboole_0(esk4_1(esk6_0))|~l1_pre_topc(k1_tex_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_43, c_0_111])).
% 0.21/0.42  cnf(c_0_115, negated_conjecture, (u1_struct_0(k1_tex_2(esk6_0,esk7_0))=esk4_1(esk6_0)|v1_xboole_0(u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_59])])).
% 0.21/0.42  cnf(c_0_116, negated_conjecture, (v1_xboole_0(esk4_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_95]), c_0_50]), c_0_59])]), c_0_68])).
% 0.21/0.42  cnf(c_0_117, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.42  cnf(c_0_118, negated_conjecture, (v2_struct_0(k1_tex_2(esk6_0,esk7_0))|v1_xboole_0(u1_struct_0(esk6_0))|~l1_struct_0(k1_tex_2(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_115]), c_0_116])])).
% 0.21/0.42  cnf(c_0_119, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|~l1_struct_0(k1_tex_2(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_50]), c_0_59])]), c_0_68])).
% 0.21/0.42  cnf(c_0_120, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|~l1_pre_topc(k1_tex_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_119, c_0_89])).
% 0.21/0.42  cnf(c_0_121, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_95]), c_0_50]), c_0_59])]), c_0_68])).
% 0.21/0.42  cnf(c_0_122, negated_conjecture, (~l1_struct_0(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_121]), c_0_68])).
% 0.21/0.42  cnf(c_0_123, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_89]), c_0_50])]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 124
% 0.21/0.42  # Proof object clause steps            : 79
% 0.21/0.42  # Proof object formula steps           : 45
% 0.21/0.42  # Proof object conjectures             : 37
% 0.21/0.42  # Proof object clause conjectures      : 34
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 28
% 0.21/0.42  # Proof object initial formulas used   : 22
% 0.21/0.42  # Proof object generating inferences   : 46
% 0.21/0.42  # Proof object simplifying inferences  : 56
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 22
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 44
% 0.21/0.42  # Removed in clause preprocessing      : 0
% 0.21/0.42  # Initial clauses in saturation        : 44
% 0.21/0.42  # Processed clauses                    : 511
% 0.21/0.42  # ...of these trivial                  : 4
% 0.21/0.42  # ...subsumed                          : 217
% 0.21/0.42  # ...remaining for further processing  : 290
% 0.21/0.42  # Other redundant clauses eliminated   : 90
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 39
% 0.21/0.42  # Backward-rewritten                   : 30
% 0.21/0.42  # Generated clauses                    : 1326
% 0.21/0.42  # ...of the previous two non-trivial   : 1091
% 0.21/0.42  # Contextual simplify-reflections      : 26
% 0.21/0.42  # Paramodulations                      : 1186
% 0.21/0.42  # Factorizations                       : 52
% 0.21/0.42  # Equation resolutions                 : 90
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 215
% 0.21/0.42  #    Positive orientable unit clauses  : 12
% 0.21/0.42  #    Positive unorientable unit clauses: 0
% 0.21/0.42  #    Negative unit clauses             : 4
% 0.21/0.42  #    Non-unit-clauses                  : 199
% 0.21/0.42  # Current number of unprocessed clauses: 558
% 0.21/0.42  # ...number of literals in the above   : 2284
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 69
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 9199
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 3621
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 254
% 0.21/0.42  # Unit Clause-clause subsumption calls : 91
% 0.21/0.42  # Rewrite failures with RHS unbound    : 0
% 0.21/0.42  # BW rewrite match attempts            : 11
% 0.21/0.42  # BW rewrite match successes           : 7
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 22714
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.073 s
% 0.21/0.43  # System time              : 0.007 s
% 0.21/0.43  # Total time               : 0.080 s
% 0.21/0.43  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
