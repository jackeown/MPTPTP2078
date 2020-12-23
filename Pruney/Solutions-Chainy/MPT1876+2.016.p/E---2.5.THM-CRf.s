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
% DateTime   : Thu Dec  3 11:20:18 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 379 expanded)
%              Number of clauses        :   54 ( 143 expanded)
%              Number of leaves         :   18 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  433 (2393 expanded)
%              Number of equality atoms :   15 (  59 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   35 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

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

fof(t44_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_tex_2(X2,X1)
          <=> v1_zfmisc_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(cc6_tdlat_3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_tdlat_3(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(cc2_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(cc2_tex_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & v2_tdlat_3(X1) )
       => ( ~ v2_struct_0(X1)
          & v7_struct_0(X1)
          & v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

fof(t34_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v1_pre_topc(X3)
                    & v1_tdlat_3(X3)
                    & m1_pre_topc(X3,X1) )
                 => X2 != u1_struct_0(X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

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

fof(c_0_18,plain,(
    ! [X34,X35,X36] :
      ( v2_struct_0(X34)
      | ~ l1_pre_topc(X34)
      | v2_struct_0(X35)
      | ~ m1_pre_topc(X35,X34)
      | ~ m1_subset_1(X36,u1_struct_0(X35))
      | m1_subset_1(X36,u1_struct_0(X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

fof(c_0_19,plain,(
    ! [X43,X44] :
      ( ( ~ v2_struct_0(esk4_2(X43,X44))
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ l1_pre_topc(X43) )
      & ( v1_pre_topc(esk4_2(X43,X44))
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ l1_pre_topc(X43) )
      & ( m1_pre_topc(esk4_2(X43,X44),X43)
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ l1_pre_topc(X43) )
      & ( X44 = u1_struct_0(esk4_2(X43,X44))
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( X1 = u1_struct_0(esk4_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk4_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v2_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v2_tex_2(X2,X1)
            <=> v1_zfmisc_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_tex_2])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X2))
    | v1_xboole_0(X4)
    | ~ m1_pre_topc(esk4_2(X1,X4),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_25,plain,
    ( m1_pre_topc(esk4_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & v2_tdlat_3(esk6_0)
    & l1_pre_topc(esk6_0)
    & ~ v1_xboole_0(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    & ( ~ v2_tex_2(esk7_0,esk6_0)
      | ~ v1_zfmisc_1(esk7_0) )
    & ( v2_tex_2(esk7_0,esk6_0)
      | v1_zfmisc_1(esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

fof(c_0_27,plain,(
    ! [X41,X42] :
      ( v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ v2_tdlat_3(X41)
      | ~ l1_pre_topc(X41)
      | ~ m1_pre_topc(X42,X41)
      | v2_tdlat_3(X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).

fof(c_0_28,plain,(
    ! [X39] :
      ( ~ l1_pre_topc(X39)
      | ~ v2_tdlat_3(X39)
      | v2_pre_topc(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X2,u1_struct_0(X1))
    | v1_xboole_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X20,X21] :
      ( ~ r2_hidden(X20,X21)
      | m1_subset_1(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_35,plain,(
    ! [X40] :
      ( ( ~ v2_struct_0(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ v1_tdlat_3(X40)
        | ~ v2_tdlat_3(X40)
        | ~ l1_pre_topc(X40) )
      & ( v7_struct_0(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ v1_tdlat_3(X40)
        | ~ v2_tdlat_3(X40)
        | ~ l1_pre_topc(X40) )
      & ( v2_pre_topc(X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ v1_tdlat_3(X40)
        | ~ v2_tdlat_3(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_1])])])])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X48,X49] :
      ( ( ~ v2_struct_0(esk5_2(X48,X49))
        | ~ v2_tex_2(X49,X48)
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( v1_pre_topc(esk5_2(X48,X49))
        | ~ v2_tex_2(X49,X48)
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( v1_tdlat_3(esk5_2(X48,X49))
        | ~ v2_tex_2(X49,X48)
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( m1_pre_topc(esk5_2(X48,X49),X48)
        | ~ v2_tex_2(X49,X48)
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( X49 = u1_struct_0(esk5_2(X48,X49))
        | ~ v2_tex_2(X49,X48)
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),c_0_32]),c_0_33])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_41,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_42,plain,(
    ! [X18,X19] :
      ( ~ v1_xboole_0(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | v1_xboole_0(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_43,plain,
    ( v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( v2_tdlat_3(X1)
    | v2_struct_0(X2)
    | ~ v2_tdlat_3(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( m1_pre_topc(esk5_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_46,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X31)
      | l1_pre_topc(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_47,plain,(
    ! [X37,X38] :
      ( v1_xboole_0(X37)
      | ~ m1_subset_1(X38,X37)
      | k6_domain_1(X37,X38) = k1_tarski(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_51,plain,(
    ! [X46,X47] :
      ( v1_xboole_0(X46)
      | v1_xboole_0(X47)
      | ~ v1_zfmisc_1(X47)
      | ~ r1_tarski(X46,X47)
      | X46 = X47 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

fof(c_0_52,plain,(
    ! [X16,X17] :
      ( ( ~ r1_tarski(k1_tarski(X16),X17)
        | r2_hidden(X16,X17) )
      & ( ~ r2_hidden(X16,X17)
        | r1_tarski(k1_tarski(X16),X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_53,plain,(
    ! [X15] : ~ v1_xboole_0(k1_tarski(X15)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_43,c_0_37])).

cnf(c_0_55,plain,
    ( v2_tdlat_3(esk5_2(X1,X2))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_37])).

cnf(c_0_56,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_57,plain,(
    ! [X51,X52] :
      ( v2_struct_0(X51)
      | ~ v2_pre_topc(X51)
      | ~ l1_pre_topc(X51)
      | ~ m1_subset_1(X52,u1_struct_0(X51))
      | v2_tex_2(k6_domain_1(u1_struct_0(X51),X52),X51) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk1_1(esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_33])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_30]),c_0_33])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_65,plain,(
    ! [X33] :
      ( ~ v7_struct_0(X33)
      | ~ l1_struct_0(X33)
      | v1_zfmisc_1(u1_struct_0(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk5_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_67,plain,
    ( v2_struct_0(esk5_2(X1,X2))
    | v2_struct_0(X1)
    | v7_struct_0(esk5_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v1_tdlat_3(esk5_2(X1,X2))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(esk5_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(esk5_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_45])).

fof(c_0_69,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk6_0),esk1_1(esk7_0)) = k1_tarski(esk1_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_73,plain,
    ( k1_tarski(X1) = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])).

cnf(c_0_74,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,plain,
    ( X1 = u1_struct_0(esk5_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(esk5_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v1_tdlat_3(esk5_2(X1,X2))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_37])).

cnf(c_0_77,plain,
    ( v1_tdlat_3(esk5_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_78,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( v2_tex_2(k1_tarski(esk1_1(esk7_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_31]),c_0_59])]),c_0_32])).

cnf(c_0_80,plain,
    ( k1_tarski(esk1_1(X1)) = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_49])).

cnf(c_0_81,negated_conjecture,
    ( v2_tex_2(esk7_0,esk6_0)
    | v1_zfmisc_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v7_struct_0(esk5_2(X1,X2))
    | ~ l1_struct_0(esk5_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(esk5_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_37])).

cnf(c_0_84,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(esk5_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_68])).

cnf(c_0_85,negated_conjecture,
    ( ~ v2_tex_2(esk7_0,esk6_0)
    | ~ v1_zfmisc_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_86,negated_conjecture,
    ( v2_tex_2(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_33]),c_0_81])).

cnf(c_0_87,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_37])).

cnf(c_0_88,negated_conjecture,
    ( v2_tdlat_3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_zfmisc_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_86]),c_0_88]),c_0_31]),c_0_30])]),c_0_32]),c_0_89]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:09:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.50/0.67  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.50/0.67  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.50/0.67  #
% 0.50/0.67  # Preprocessing time       : 0.031 s
% 0.50/0.67  # Presaturation interreduction done
% 0.50/0.67  
% 0.50/0.67  # Proof found!
% 0.50/0.67  # SZS status Theorem
% 0.50/0.67  # SZS output start CNFRefutation
% 0.50/0.67  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.50/0.67  fof(t10_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>?[X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&X2=u1_struct_0(X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 0.50/0.67  fof(t44_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 0.50/0.67  fof(cc6_tdlat_3, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_tdlat_3(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 0.50/0.67  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 0.50/0.67  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.50/0.67  fof(cc2_tex_1, axiom, ![X1]:(l1_pre_topc(X1)=>((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&v2_tdlat_3(X1))=>((~(v2_struct_0(X1))&v7_struct_0(X1))&v2_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 0.50/0.67  fof(t34_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v2_tex_2(X2,X1)&![X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&v1_tdlat_3(X3))&m1_pre_topc(X3,X1))=>X2!=u1_struct_0(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 0.50/0.67  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.50/0.67  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.50/0.67  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.50/0.67  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.50/0.67  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.50/0.67  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.50/0.67  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.50/0.67  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 0.50/0.67  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.50/0.67  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.50/0.67  fof(c_0_18, plain, ![X34, X35, X36]:(v2_struct_0(X34)|~l1_pre_topc(X34)|(v2_struct_0(X35)|~m1_pre_topc(X35,X34)|(~m1_subset_1(X36,u1_struct_0(X35))|m1_subset_1(X36,u1_struct_0(X34))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.50/0.67  fof(c_0_19, plain, ![X43, X44]:((((~v2_struct_0(esk4_2(X43,X44))|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))))|(v2_struct_0(X43)|~l1_pre_topc(X43)))&(v1_pre_topc(esk4_2(X43,X44))|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))))|(v2_struct_0(X43)|~l1_pre_topc(X43))))&(m1_pre_topc(esk4_2(X43,X44),X43)|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))))|(v2_struct_0(X43)|~l1_pre_topc(X43))))&(X44=u1_struct_0(esk4_2(X43,X44))|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))))|(v2_struct_0(X43)|~l1_pre_topc(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).
% 0.50/0.67  cnf(c_0_20, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.67  cnf(c_0_21, plain, (X1=u1_struct_0(esk4_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.50/0.67  cnf(c_0_22, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk4_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.50/0.67  fof(c_0_23, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t44_tex_2])).
% 0.50/0.67  cnf(c_0_24, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X2))|v1_xboole_0(X4)|~m1_pre_topc(esk4_2(X1,X4),X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.50/0.67  cnf(c_0_25, plain, (m1_pre_topc(esk4_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.50/0.67  fof(c_0_26, negated_conjecture, ((((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&v2_tdlat_3(esk6_0))&l1_pre_topc(esk6_0))&((~v1_xboole_0(esk7_0)&m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))))&((~v2_tex_2(esk7_0,esk6_0)|~v1_zfmisc_1(esk7_0))&(v2_tex_2(esk7_0,esk6_0)|v1_zfmisc_1(esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 0.50/0.67  fof(c_0_27, plain, ![X41, X42]:(v2_struct_0(X41)|~v2_pre_topc(X41)|~v2_tdlat_3(X41)|~l1_pre_topc(X41)|(~m1_pre_topc(X42,X41)|v2_tdlat_3(X42))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).
% 0.50/0.67  fof(c_0_28, plain, ![X39]:(~l1_pre_topc(X39)|(~v2_tdlat_3(X39)|v2_pre_topc(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 0.50/0.67  cnf(c_0_29, plain, (v2_struct_0(X1)|m1_subset_1(X2,u1_struct_0(X1))|v1_xboole_0(X3)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.50/0.67  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.67  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.67  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.67  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.67  fof(c_0_34, plain, ![X20, X21]:(~r2_hidden(X20,X21)|m1_subset_1(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.50/0.67  fof(c_0_35, plain, ![X40]:(((~v2_struct_0(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~v1_tdlat_3(X40)|~v2_tdlat_3(X40))|~l1_pre_topc(X40))&(v7_struct_0(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~v1_tdlat_3(X40)|~v2_tdlat_3(X40))|~l1_pre_topc(X40)))&(v2_pre_topc(X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~v1_tdlat_3(X40)|~v2_tdlat_3(X40))|~l1_pre_topc(X40))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_1])])])])).
% 0.50/0.67  cnf(c_0_36, plain, (v2_struct_0(X1)|v2_tdlat_3(X2)|~v2_pre_topc(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.50/0.67  cnf(c_0_37, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.50/0.67  fof(c_0_38, plain, ![X48, X49]:(((((~v2_struct_0(esk5_2(X48,X49))|~v2_tex_2(X49,X48)|(v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48))))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))&(v1_pre_topc(esk5_2(X48,X49))|~v2_tex_2(X49,X48)|(v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48))))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48))))&(v1_tdlat_3(esk5_2(X48,X49))|~v2_tex_2(X49,X48)|(v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48))))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48))))&(m1_pre_topc(esk5_2(X48,X49),X48)|~v2_tex_2(X49,X48)|(v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48))))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48))))&(X49=u1_struct_0(esk5_2(X48,X49))|~v2_tex_2(X49,X48)|(v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48))))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).
% 0.50/0.67  cnf(c_0_39, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk6_0))|~m1_subset_1(X1,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])]), c_0_32]), c_0_33])).
% 0.50/0.67  cnf(c_0_40, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.50/0.67  fof(c_0_41, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.50/0.67  fof(c_0_42, plain, ![X18, X19]:(~v1_xboole_0(X18)|(~m1_subset_1(X19,k1_zfmisc_1(X18))|v1_xboole_0(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.50/0.67  cnf(c_0_43, plain, (v7_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.50/0.67  cnf(c_0_44, plain, (v2_tdlat_3(X1)|v2_struct_0(X2)|~v2_tdlat_3(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_36, c_0_37])).
% 0.50/0.67  cnf(c_0_45, plain, (m1_pre_topc(esk5_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.50/0.67  fof(c_0_46, plain, ![X31, X32]:(~l1_pre_topc(X31)|(~m1_pre_topc(X32,X31)|l1_pre_topc(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.50/0.67  fof(c_0_47, plain, ![X37, X38]:(v1_xboole_0(X37)|~m1_subset_1(X38,X37)|k6_domain_1(X37,X38)=k1_tarski(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.50/0.67  cnf(c_0_48, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.50/0.67  cnf(c_0_49, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.50/0.67  cnf(c_0_50, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.50/0.67  fof(c_0_51, plain, ![X46, X47]:(v1_xboole_0(X46)|(v1_xboole_0(X47)|~v1_zfmisc_1(X47)|(~r1_tarski(X46,X47)|X46=X47))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.50/0.67  fof(c_0_52, plain, ![X16, X17]:((~r1_tarski(k1_tarski(X16),X17)|r2_hidden(X16,X17))&(~r2_hidden(X16,X17)|r1_tarski(k1_tarski(X16),X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.50/0.67  fof(c_0_53, plain, ![X15]:~v1_xboole_0(k1_tarski(X15)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.50/0.67  cnf(c_0_54, plain, (v2_struct_0(X1)|v7_struct_0(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_43, c_0_37])).
% 0.50/0.67  cnf(c_0_55, plain, (v2_tdlat_3(esk5_2(X1,X2))|v2_struct_0(X1)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_37])).
% 0.50/0.67  cnf(c_0_56, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.50/0.67  fof(c_0_57, plain, ![X51, X52]:(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)|(~m1_subset_1(X52,u1_struct_0(X51))|v2_tex_2(k6_domain_1(u1_struct_0(X51),X52),X51))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 0.50/0.67  cnf(c_0_58, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.50/0.67  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk1_1(esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_33])).
% 0.50/0.67  cnf(c_0_60, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_30]), c_0_33])).
% 0.50/0.67  cnf(c_0_61, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.50/0.67  cnf(c_0_62, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.50/0.67  cnf(c_0_63, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.50/0.67  cnf(c_0_64, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.50/0.67  fof(c_0_65, plain, ![X33]:(~v7_struct_0(X33)|~l1_struct_0(X33)|v1_zfmisc_1(u1_struct_0(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.50/0.67  cnf(c_0_66, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk5_2(X1,X2))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.50/0.67  cnf(c_0_67, plain, (v2_struct_0(esk5_2(X1,X2))|v2_struct_0(X1)|v7_struct_0(esk5_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v1_tdlat_3(esk5_2(X1,X2))|~v2_tdlat_3(X1)|~l1_pre_topc(esk5_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.50/0.67  cnf(c_0_68, plain, (v2_struct_0(X1)|l1_pre_topc(esk5_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_56, c_0_45])).
% 0.50/0.67  fof(c_0_69, plain, ![X30]:(~l1_pre_topc(X30)|l1_struct_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.50/0.67  cnf(c_0_70, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.50/0.67  cnf(c_0_71, negated_conjecture, (k6_domain_1(u1_struct_0(esk6_0),esk1_1(esk7_0))=k1_tarski(esk1_1(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.50/0.67  cnf(c_0_72, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.67  cnf(c_0_73, plain, (k1_tarski(X1)=X2|~v1_zfmisc_1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])).
% 0.50/0.67  cnf(c_0_74, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.50/0.67  cnf(c_0_75, plain, (X1=u1_struct_0(esk5_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.50/0.67  cnf(c_0_76, plain, (v2_struct_0(X1)|v7_struct_0(esk5_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v1_tdlat_3(esk5_2(X1,X2))|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_37])).
% 0.50/0.67  cnf(c_0_77, plain, (v1_tdlat_3(esk5_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.50/0.67  cnf(c_0_78, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.50/0.67  cnf(c_0_79, negated_conjecture, (v2_tex_2(k1_tarski(esk1_1(esk7_0)),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_31]), c_0_59])]), c_0_32])).
% 0.50/0.67  cnf(c_0_80, plain, (k1_tarski(esk1_1(X1))=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_49])).
% 0.50/0.67  cnf(c_0_81, negated_conjecture, (v2_tex_2(esk7_0,esk6_0)|v1_zfmisc_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.67  cnf(c_0_82, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v7_struct_0(esk5_2(X1,X2))|~l1_struct_0(esk5_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.50/0.67  cnf(c_0_83, plain, (v2_struct_0(X1)|v7_struct_0(esk5_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_37])).
% 0.50/0.67  cnf(c_0_84, plain, (v2_struct_0(X1)|l1_struct_0(esk5_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_78, c_0_68])).
% 0.50/0.67  cnf(c_0_85, negated_conjecture, (~v2_tex_2(esk7_0,esk6_0)|~v1_zfmisc_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.67  cnf(c_0_86, negated_conjecture, (v2_tex_2(esk7_0,esk6_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_33]), c_0_81])).
% 0.50/0.67  cnf(c_0_87, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_37])).
% 0.50/0.67  cnf(c_0_88, negated_conjecture, (v2_tdlat_3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.67  cnf(c_0_89, negated_conjecture, (~v1_zfmisc_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 0.50/0.67  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_86]), c_0_88]), c_0_31]), c_0_30])]), c_0_32]), c_0_89]), c_0_33]), ['proof']).
% 0.50/0.67  # SZS output end CNFRefutation
% 0.50/0.67  # Proof object total steps             : 91
% 0.50/0.67  # Proof object clause steps            : 54
% 0.50/0.67  # Proof object formula steps           : 37
% 0.50/0.67  # Proof object conjectures             : 20
% 0.50/0.67  # Proof object clause conjectures      : 17
% 0.50/0.67  # Proof object formula conjectures     : 3
% 0.50/0.67  # Proof object initial clauses used    : 31
% 0.50/0.67  # Proof object initial formulas used   : 18
% 0.50/0.67  # Proof object generating inferences   : 20
% 0.50/0.67  # Proof object simplifying inferences  : 34
% 0.50/0.67  # Training examples: 0 positive, 0 negative
% 0.50/0.67  # Parsed axioms                        : 22
% 0.50/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.67  # Initial clauses                      : 44
% 0.50/0.67  # Removed in clause preprocessing      : 2
% 0.50/0.67  # Initial clauses in saturation        : 42
% 0.50/0.67  # Processed clauses                    : 3092
% 0.50/0.67  # ...of these trivial                  : 2
% 0.50/0.67  # ...subsumed                          : 2269
% 0.50/0.67  # ...remaining for further processing  : 821
% 0.50/0.67  # Other redundant clauses eliminated   : 7
% 0.50/0.67  # Clauses deleted for lack of memory   : 0
% 0.50/0.67  # Backward-subsumed                    : 44
% 0.50/0.67  # Backward-rewritten                   : 3
% 0.50/0.67  # Generated clauses                    : 10490
% 0.50/0.67  # ...of the previous two non-trivial   : 10092
% 0.50/0.67  # Contextual simplify-reflections      : 115
% 0.50/0.67  # Paramodulations                      : 10482
% 0.50/0.67  # Factorizations                       : 2
% 0.50/0.67  # Equation resolutions                 : 7
% 0.50/0.67  # Propositional unsat checks           : 0
% 0.50/0.67  #    Propositional check models        : 0
% 0.50/0.67  #    Propositional check unsatisfiable : 0
% 0.50/0.67  #    Propositional clauses             : 0
% 0.50/0.67  #    Propositional clauses after purity: 0
% 0.50/0.67  #    Propositional unsat core size     : 0
% 0.50/0.67  #    Propositional preprocessing time  : 0.000
% 0.50/0.67  #    Propositional encoding time       : 0.000
% 0.50/0.67  #    Propositional solver time         : 0.000
% 0.50/0.67  #    Success case prop preproc time    : 0.000
% 0.50/0.67  #    Success case prop encoding time   : 0.000
% 0.50/0.67  #    Success case prop solver time     : 0.000
% 0.50/0.67  # Current number of processed clauses  : 730
% 0.50/0.67  #    Positive orientable unit clauses  : 18
% 0.50/0.67  #    Positive unorientable unit clauses: 0
% 0.50/0.67  #    Negative unit clauses             : 5
% 0.50/0.67  #    Non-unit-clauses                  : 707
% 0.50/0.67  # Current number of unprocessed clauses: 7001
% 0.50/0.67  # ...number of literals in the above   : 50336
% 0.50/0.67  # Current number of archived formulas  : 0
% 0.50/0.67  # Current number of archived clauses   : 89
% 0.50/0.67  # Clause-clause subsumption calls (NU) : 213020
% 0.50/0.67  # Rec. Clause-clause subsumption calls : 26849
% 0.50/0.67  # Non-unit clause-clause subsumptions  : 1898
% 0.50/0.67  # Unit Clause-clause subsumption calls : 267
% 0.50/0.67  # Rewrite failures with RHS unbound    : 0
% 0.50/0.67  # BW rewrite match attempts            : 2
% 0.50/0.67  # BW rewrite match successes           : 2
% 0.50/0.67  # Condensation attempts                : 0
% 0.50/0.67  # Condensation successes               : 0
% 0.50/0.67  # Termbank termtop insertions          : 274002
% 0.50/0.67  
% 0.50/0.67  # -------------------------------------------------
% 0.50/0.67  # User time                : 0.312 s
% 0.50/0.67  # System time              : 0.010 s
% 0.50/0.67  # Total time               : 0.322 s
% 0.50/0.67  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
