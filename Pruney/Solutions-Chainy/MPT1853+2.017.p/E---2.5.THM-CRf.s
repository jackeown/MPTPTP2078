%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:27 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 334 expanded)
%              Number of clauses        :   53 ( 122 expanded)
%              Number of leaves         :   17 (  83 expanded)
%              Depth                    :   20
%              Number of atoms          :  342 (1502 expanded)
%              Number of equality atoms :   24 (  34 expanded)
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

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

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

fof(fc6_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ( ~ v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)) )
    & ( v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_19,plain,(
    ! [X34,X35] :
      ( ( ~ v1_subset_1(X35,X34)
        | X35 != X34
        | ~ m1_subset_1(X35,k1_zfmisc_1(X34)) )
      & ( X35 = X34
        | v1_subset_1(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X21)
      | ~ m1_subset_1(X22,X21)
      | m1_subset_1(k6_domain_1(X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_23,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v1_tex_2(X31,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | X32 != u1_struct_0(X31)
        | v1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_pre_topc(X31,X30)
        | ~ l1_pre_topc(X30) )
      & ( m1_subset_1(esk4_2(X30,X31),k1_zfmisc_1(u1_struct_0(X30)))
        | v1_tex_2(X31,X30)
        | ~ m1_pre_topc(X31,X30)
        | ~ l1_pre_topc(X30) )
      & ( esk4_2(X30,X31) = u1_struct_0(X31)
        | v1_tex_2(X31,X30)
        | ~ m1_pre_topc(X31,X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ v1_subset_1(esk4_2(X30,X31),u1_struct_0(X30))
        | v1_tex_2(X31,X30)
        | ~ m1_pre_topc(X31,X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_24,plain,(
    ! [X27,X29] :
      ( ( m1_subset_1(esk3_1(X27),X27)
        | ~ v1_zfmisc_1(X27)
        | v1_xboole_0(X27) )
      & ( X27 = k6_domain_1(X27,esk3_1(X27))
        | ~ v1_zfmisc_1(X27)
        | v1_xboole_0(X27) )
      & ( ~ m1_subset_1(X29,X27)
        | X27 != k6_domain_1(X27,X29)
        | v1_zfmisc_1(X27)
        | v1_xboole_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

cnf(c_0_25,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk5_0),esk6_0) = u1_struct_0(esk5_0)
    | ~ v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X2 != k6_domain_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk5_0),esk6_0) = u1_struct_0(esk5_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_32,plain,
    ( esk4_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( esk4_2(X1,X2) = u1_struct_0(X1)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_29])).

fof(c_0_34,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | l1_pre_topc(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_35,plain,(
    ! [X36,X37] :
      ( ( ~ v2_struct_0(k1_tex_2(X36,X37))
        | v2_struct_0(X36)
        | ~ l1_pre_topc(X36)
        | ~ m1_subset_1(X37,u1_struct_0(X36)) )
      & ( v1_pre_topc(k1_tex_2(X36,X37))
        | v2_struct_0(X36)
        | ~ l1_pre_topc(X36)
        | ~ m1_subset_1(X37,u1_struct_0(X36)) )
      & ( m1_pre_topc(k1_tex_2(X36,X37),X36)
        | v2_struct_0(X36)
        | ~ l1_pre_topc(X36)
        | ~ m1_subset_1(X37,u1_struct_0(X36)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_36,plain,(
    ! [X40,X41] :
      ( v2_struct_0(X40)
      | ~ l1_struct_0(X40)
      | ~ m1_subset_1(X41,u1_struct_0(X40))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X40),X41),u1_struct_0(X40))
      | ~ v7_struct_0(X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

fof(c_0_37,plain,(
    ! [X20] :
      ( ~ v7_struct_0(X20)
      | ~ l1_struct_0(X20)
      | v1_zfmisc_1(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_38,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_27])])).

cnf(c_0_39,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_41,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | l1_struct_0(X16) ) ),
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
    ! [X25,X26] :
      ( ( ~ v2_struct_0(X26)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v7_struct_0(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ v1_tex_2(X26,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v7_struct_0(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk5_0,esk6_0)) = u1_struct_0(esk5_0)
    | v1_zfmisc_1(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0) ),
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
    ( v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)
    | ~ v7_struct_0(esk5_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_27])]),c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v7_struct_0(k1_tex_2(esk5_0,esk6_0))
    | ~ m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0)
    | ~ l1_struct_0(k1_tex_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_56,plain,(
    ! [X38,X39] :
      ( ( ~ v2_struct_0(k1_tex_2(X38,X39))
        | v2_struct_0(X38)
        | ~ l1_pre_topc(X38)
        | ~ m1_subset_1(X39,u1_struct_0(X38)) )
      & ( v7_struct_0(k1_tex_2(X38,X39))
        | v2_struct_0(X38)
        | ~ l1_pre_topc(X38)
        | ~ m1_subset_1(X39,u1_struct_0(X38)) )
      & ( v1_pre_topc(k1_tex_2(X38,X39))
        | v2_struct_0(X38)
        | ~ l1_pre_topc(X38)
        | ~ m1_subset_1(X39,u1_struct_0(X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk5_0,esk6_0))
    | ~ v7_struct_0(esk5_0)
    | ~ m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_40])]),c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_40])).

cnf(c_0_59,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v7_struct_0(k1_tex_2(esk5_0,esk6_0))
    | ~ m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0) ),
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
    ( v2_struct_0(k1_tex_2(esk5_0,esk6_0))
    | ~ v7_struct_0(esk5_0)
    | ~ m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

fof(c_0_63,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_64,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_65,plain,(
    ! [X19] :
      ( v7_struct_0(X19)
      | ~ l1_struct_0(X19)
      | ~ v1_zfmisc_1(u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).

cnf(c_0_66,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_27]),c_0_40])]),c_0_47])).

cnf(c_0_67,negated_conjecture,
    ( ~ v7_struct_0(esk5_0)
    | ~ m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_27]),c_0_40])]),c_0_47])).

cnf(c_0_68,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,plain,
    ( v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_43]),c_0_27]),c_0_40])]),c_0_47])).

cnf(c_0_72,negated_conjecture,
    ( ~ v7_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_43]),c_0_27]),c_0_40])]),c_0_47])).

fof(c_0_73,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_58])]),c_0_72])).

fof(c_0_76,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | r1_tarski(u1_struct_0(X24),u1_struct_0(X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( X1 = u1_struct_0(esk5_0)
    | ~ r1_tarski(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,plain,
    ( v2_struct_0(X1)
    | r1_tarski(u1_struct_0(k1_tex_2(X1,X2)),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_43])).

cnf(c_0_82,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk5_0,X1)) = u1_struct_0(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_40])]),c_0_47])).

cnf(c_0_83,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v7_struct_0(k1_tex_2(esk5_0,X1))
    | ~ l1_struct_0(k1_tex_2(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v7_struct_0(k1_tex_2(esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_55]),c_0_40])]),c_0_47])).

cnf(c_0_85,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_60]),c_0_40])]),c_0_47])).

cnf(c_0_86,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_27])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_86]),c_0_58])]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 0.13/0.38  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.13/0.38  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.13/0.38  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.13/0.38  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.13/0.38  fof(t8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~((v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))&v7_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 0.13/0.38  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(cc10_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v7_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(~(v2_struct_0(X2))=>(~(v2_struct_0(X2))&~(v1_tex_2(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 0.13/0.38  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.13/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.38  fof(fc6_struct_0, axiom, ![X1]:((~(v7_struct_0(X1))&l1_struct_0(X1))=>~(v1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.13/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.13/0.38  fof(c_0_18, negated_conjecture, ((~v2_struct_0(esk5_0)&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&((~v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)))&(v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.13/0.38  fof(c_0_19, plain, ![X34, X35]:((~v1_subset_1(X35,X34)|X35!=X34|~m1_subset_1(X35,k1_zfmisc_1(X34)))&(X35=X34|v1_subset_1(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (~v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_21, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_22, plain, ![X21, X22]:(v1_xboole_0(X21)|~m1_subset_1(X22,X21)|m1_subset_1(k6_domain_1(X21,X22),k1_zfmisc_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.13/0.38  fof(c_0_23, plain, ![X30, X31, X32]:((~v1_tex_2(X31,X30)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|(X32!=u1_struct_0(X31)|v1_subset_1(X32,u1_struct_0(X30))))|~m1_pre_topc(X31,X30)|~l1_pre_topc(X30))&((m1_subset_1(esk4_2(X30,X31),k1_zfmisc_1(u1_struct_0(X30)))|v1_tex_2(X31,X30)|~m1_pre_topc(X31,X30)|~l1_pre_topc(X30))&((esk4_2(X30,X31)=u1_struct_0(X31)|v1_tex_2(X31,X30)|~m1_pre_topc(X31,X30)|~l1_pre_topc(X30))&(~v1_subset_1(esk4_2(X30,X31),u1_struct_0(X30))|v1_tex_2(X31,X30)|~m1_pre_topc(X31,X30)|~l1_pre_topc(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.13/0.38  fof(c_0_24, plain, ![X27, X29]:(((m1_subset_1(esk3_1(X27),X27)|~v1_zfmisc_1(X27)|v1_xboole_0(X27))&(X27=k6_domain_1(X27,esk3_1(X27))|~v1_zfmisc_1(X27)|v1_xboole_0(X27)))&(~m1_subset_1(X29,X27)|X27!=k6_domain_1(X27,X29)|v1_zfmisc_1(X27)|v1_xboole_0(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (k6_domain_1(u1_struct_0(esk5_0),esk6_0)=u1_struct_0(esk5_0)|~v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)|~m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  cnf(c_0_26, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_28, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_29, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_30, plain, (v1_zfmisc_1(X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)|X2!=k6_domain_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (k6_domain_1(u1_struct_0(esk5_0),esk6_0)=u1_struct_0(esk5_0)|v1_xboole_0(u1_struct_0(esk5_0))|~v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.13/0.38  cnf(c_0_32, plain, (esk4_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_33, plain, (esk4_2(X1,X2)=u1_struct_0(X1)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_21]), c_0_29])).
% 0.13/0.38  fof(c_0_34, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|l1_pre_topc(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  fof(c_0_35, plain, ![X36, X37]:(((~v2_struct_0(k1_tex_2(X36,X37))|(v2_struct_0(X36)|~l1_pre_topc(X36)|~m1_subset_1(X37,u1_struct_0(X36))))&(v1_pre_topc(k1_tex_2(X36,X37))|(v2_struct_0(X36)|~l1_pre_topc(X36)|~m1_subset_1(X37,u1_struct_0(X36)))))&(m1_pre_topc(k1_tex_2(X36,X37),X36)|(v2_struct_0(X36)|~l1_pre_topc(X36)|~m1_subset_1(X37,u1_struct_0(X36))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.13/0.38  fof(c_0_36, plain, ![X40, X41]:(v2_struct_0(X40)|~l1_struct_0(X40)|(~m1_subset_1(X41,u1_struct_0(X40))|(~v1_subset_1(k6_domain_1(u1_struct_0(X40),X41),u1_struct_0(X40))|~v7_struct_0(X40)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).
% 0.13/0.38  fof(c_0_37, plain, ![X20]:(~v7_struct_0(X20)|~l1_struct_0(X20)|v1_zfmisc_1(u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))|~v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_27])])).
% 0.13/0.38  cnf(c_0_39, plain, (u1_struct_0(X1)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_41, plain, ![X16]:(~l1_pre_topc(X16)|l1_struct_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  cnf(c_0_42, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_43, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  fof(c_0_44, plain, ![X25, X26]:((~v2_struct_0(X26)|v2_struct_0(X26)|~m1_pre_topc(X26,X25)|(v2_struct_0(X25)|~v7_struct_0(X25)|~l1_pre_topc(X25)))&(~v1_tex_2(X26,X25)|v2_struct_0(X26)|~m1_pre_topc(X26,X25)|(v2_struct_0(X25)|~v7_struct_0(X25)|~l1_pre_topc(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).
% 0.13/0.38  cnf(c_0_45, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~v7_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_48, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (u1_struct_0(k1_tex_2(esk5_0,esk6_0))=u1_struct_0(esk5_0)|v1_zfmisc_1(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))|~m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.13/0.38  cnf(c_0_50, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_51, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_52, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~v7_struct_0(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (v1_tex_2(k1_tex_2(esk5_0,esk6_0),esk5_0)|~v7_struct_0(esk5_0)|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_27])]), c_0_47])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))|~v7_struct_0(k1_tex_2(esk5_0,esk6_0))|~m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0)|~l1_struct_0(k1_tex_2(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_55, plain, (v2_struct_0(X1)|l1_struct_0(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.38  fof(c_0_56, plain, ![X38, X39]:(((~v2_struct_0(k1_tex_2(X38,X39))|(v2_struct_0(X38)|~l1_pre_topc(X38)|~m1_subset_1(X39,u1_struct_0(X38))))&(v7_struct_0(k1_tex_2(X38,X39))|(v2_struct_0(X38)|~l1_pre_topc(X38)|~m1_subset_1(X39,u1_struct_0(X38)))))&(v1_pre_topc(k1_tex_2(X38,X39))|(v2_struct_0(X38)|~l1_pre_topc(X38)|~m1_subset_1(X39,u1_struct_0(X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (v2_struct_0(k1_tex_2(esk5_0,esk6_0))|~v7_struct_0(esk5_0)|~m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0)|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_40])]), c_0_47])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_40])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))|~v7_struct_0(k1_tex_2(esk5_0,esk6_0))|~m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_27]), c_0_40])]), c_0_47])).
% 0.13/0.38  cnf(c_0_60, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.38  cnf(c_0_61, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (v2_struct_0(k1_tex_2(esk5_0,esk6_0))|~v7_struct_0(esk5_0)|~m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 0.13/0.38  fof(c_0_63, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.38  fof(c_0_64, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.38  fof(c_0_65, plain, ![X19]:(v7_struct_0(X19)|~l1_struct_0(X19)|~v1_zfmisc_1(u1_struct_0(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))|~m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_27]), c_0_40])]), c_0_47])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (~v7_struct_0(esk5_0)|~m1_pre_topc(k1_tex_2(esk5_0,esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_27]), c_0_40])]), c_0_47])).
% 0.13/0.38  cnf(c_0_68, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.38  cnf(c_0_69, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.38  cnf(c_0_70, plain, (v7_struct_0(X1)|~l1_struct_0(X1)|~v1_zfmisc_1(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_43]), c_0_27]), c_0_40])]), c_0_47])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (~v7_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_43]), c_0_27]), c_0_40])]), c_0_47])).
% 0.13/0.38  fof(c_0_73, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  cnf(c_0_74, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_58])]), c_0_72])).
% 0.13/0.38  fof(c_0_76, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_pre_topc(X24,X23)|r1_tarski(u1_struct_0(X24),u1_struct_0(X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.13/0.38  cnf(c_0_77, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (r1_tarski(u1_struct_0(esk5_0),X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.13/0.38  cnf(c_0_79, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.13/0.38  cnf(c_0_80, negated_conjecture, (X1=u1_struct_0(esk5_0)|~r1_tarski(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.13/0.38  cnf(c_0_81, plain, (v2_struct_0(X1)|r1_tarski(u1_struct_0(k1_tex_2(X1,X2)),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_79, c_0_43])).
% 0.13/0.38  cnf(c_0_82, negated_conjecture, (u1_struct_0(k1_tex_2(esk5_0,X1))=u1_struct_0(esk5_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_40])]), c_0_47])).
% 0.13/0.38  cnf(c_0_83, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~v7_struct_0(k1_tex_2(esk5_0,X1))|~l1_struct_0(k1_tex_2(esk5_0,X1))), inference(spm,[status(thm)],[c_0_48, c_0_82])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~v7_struct_0(k1_tex_2(esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_55]), c_0_40])]), c_0_47])).
% 0.13/0.38  cnf(c_0_85, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_60]), c_0_40])]), c_0_47])).
% 0.13/0.38  cnf(c_0_86, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_85, c_0_27])).
% 0.13/0.38  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_86]), c_0_58])]), c_0_72]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 88
% 0.13/0.38  # Proof object clause steps            : 53
% 0.13/0.38  # Proof object formula steps           : 35
% 0.13/0.38  # Proof object conjectures             : 31
% 0.13/0.38  # Proof object clause conjectures      : 28
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 24
% 0.13/0.38  # Proof object initial formulas used   : 17
% 0.13/0.38  # Proof object generating inferences   : 28
% 0.13/0.38  # Proof object simplifying inferences  : 50
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 17
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 37
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 36
% 0.13/0.38  # Processed clauses                    : 131
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 12
% 0.13/0.38  # ...remaining for further processing  : 118
% 0.13/0.38  # Other redundant clauses eliminated   : 4
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 12
% 0.13/0.38  # Backward-rewritten                   : 9
% 0.13/0.38  # Generated clauses                    : 130
% 0.13/0.38  # ...of the previous two non-trivial   : 112
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 126
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 4
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 60
% 0.13/0.38  #    Positive orientable unit clauses  : 7
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 51
% 0.13/0.38  # Current number of unprocessed clauses: 47
% 0.13/0.38  # ...number of literals in the above   : 308
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 54
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 860
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 306
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 23
% 0.13/0.38  # Unit Clause-clause subsumption calls : 15
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 7
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5850
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.036 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.042 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
