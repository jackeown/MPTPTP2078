%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:17 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 269 expanded)
%              Number of clauses        :   48 ( 103 expanded)
%              Number of leaves         :   18 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  364 (1526 expanded)
%              Number of equality atoms :   11 (  29 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   35 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

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

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

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

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

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

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | m1_subset_1(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & v2_tdlat_3(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v1_xboole_0(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ( ~ v2_tex_2(esk6_0,esk5_0)
      | ~ v1_zfmisc_1(esk6_0) )
    & ( v2_tex_2(esk6_0,esk5_0)
      | v1_zfmisc_1(esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_21,plain,(
    ! [X38,X39] :
      ( v2_struct_0(X38)
      | ~ v2_pre_topc(X38)
      | ~ v2_tdlat_3(X38)
      | ~ l1_pre_topc(X38)
      | ~ m1_pre_topc(X39,X38)
      | v2_tdlat_3(X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).

fof(c_0_22,plain,(
    ! [X36] :
      ( ~ l1_pre_topc(X36)
      | ~ v2_tdlat_3(X36)
      | v2_pre_topc(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_26,plain,(
    ! [X22,X23] :
      ( ~ v1_xboole_0(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | v1_xboole_0(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_27,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_28,plain,(
    ! [X20,X21] :
      ( ~ r2_hidden(X20,X21)
      | m1_subset_1(k1_tarski(X20),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_29,plain,(
    ! [X37] :
      ( ( ~ v2_struct_0(X37)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ v1_tdlat_3(X37)
        | ~ v2_tdlat_3(X37)
        | ~ l1_pre_topc(X37) )
      & ( v7_struct_0(X37)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ v1_tdlat_3(X37)
        | ~ v2_tdlat_3(X37)
        | ~ l1_pre_topc(X37) )
      & ( v2_pre_topc(X37)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ v1_tdlat_3(X37)
        | ~ v2_tdlat_3(X37)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_1])])])])).

fof(c_0_30,plain,(
    ! [X35] :
      ( ~ l1_pre_topc(X35)
      | ~ v1_tdlat_3(X35)
      | v2_pre_topc(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X42,X43] :
      ( ( ~ v2_struct_0(esk4_2(X42,X43))
        | ~ v2_tex_2(X43,X42)
        | v1_xboole_0(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( v1_pre_topc(esk4_2(X42,X43))
        | ~ v2_tex_2(X43,X42)
        | v1_xboole_0(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( v1_tdlat_3(esk4_2(X42,X43))
        | ~ v2_tex_2(X43,X42)
        | v1_xboole_0(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( m1_pre_topc(esk4_2(X42,X43),X42)
        | ~ v2_tex_2(X43,X42)
        | v1_xboole_0(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) )
      & ( X43 = u1_struct_0(esk4_2(X42,X43))
        | ~ v2_tex_2(X43,X42)
        | v1_xboole_0(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

fof(c_0_34,plain,(
    ! [X33,X34] :
      ( v1_xboole_0(X33)
      | ~ m1_subset_1(X34,X33)
      | k6_domain_1(X33,X34) = k1_tarski(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_44,plain,
    ( m1_pre_topc(esk4_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_45,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | l1_pre_topc(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_46,plain,(
    ! [X45,X46] :
      ( v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,u1_struct_0(X45))
      | v2_tex_2(k6_domain_1(u1_struct_0(X45),X46),X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk1_1(esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_24]),c_0_37])).

fof(c_0_50,plain,(
    ! [X40,X41] :
      ( v1_xboole_0(X40)
      | v1_xboole_0(X41)
      | ~ v1_zfmisc_1(X41)
      | ~ r1_tarski(X40,X41)
      | X40 = X41 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_52,plain,(
    ! [X17] : ~ v1_xboole_0(k1_tarski(X17)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_53,plain,(
    ! [X32] :
      ( ~ v7_struct_0(X32)
      | ~ l1_struct_0(X32)
      | v1_zfmisc_1(u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(esk4_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_32])).

cnf(c_0_56,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_57,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk5_0),esk1_1(esk6_0)) = k1_tarski(esk1_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_tarski(esk1_1(X1)),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_36])).

cnf(c_0_65,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,plain,
    ( X1 = u1_struct_0(esk4_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_68,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk4_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_69,plain,
    ( v2_struct_0(esk4_2(X1,X2))
    | v2_struct_0(X1)
    | v7_struct_0(esk4_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(esk4_2(X1,X2))
    | ~ l1_pre_topc(esk4_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(esk4_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_44])).

cnf(c_0_71,plain,
    ( v1_tdlat_3(esk4_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_72,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_73,negated_conjecture,
    ( v2_tex_2(k1_tarski(esk1_1(esk6_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_48])]),c_0_62])).

cnf(c_0_74,plain,
    ( k1_tarski(esk1_1(X1)) = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0)
    | v1_zfmisc_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v7_struct_0(esk4_2(X1,X2))
    | ~ l1_struct_0(esk4_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(esk4_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71]),c_0_32])).

cnf(c_0_78,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(esk4_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( ~ v2_tex_2(esk6_0,esk5_0)
    | ~ v1_zfmisc_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_80,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_37]),c_0_75])).

cnf(c_0_81,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_32])).

cnf(c_0_82,negated_conjecture,
    ( v2_tdlat_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_zfmisc_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_80]),c_0_82]),c_0_61]),c_0_24])]),c_0_62]),c_0_83]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 2.54/2.70  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 2.54/2.70  # and selection function SelectMaxLComplexAvoidPosPred.
% 2.54/2.70  #
% 2.54/2.70  # Preprocessing time       : 0.025 s
% 2.54/2.70  # Presaturation interreduction done
% 2.54/2.70  
% 2.54/2.70  # Proof found!
% 2.54/2.70  # SZS status Theorem
% 2.54/2.70  # SZS output start CNFRefutation
% 2.54/2.70  fof(t44_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 2.54/2.70  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.54/2.70  fof(cc6_tdlat_3, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_tdlat_3(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 2.54/2.70  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 2.54/2.70  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.54/2.70  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.54/2.70  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.54/2.70  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.54/2.70  fof(cc2_tex_1, axiom, ![X1]:(l1_pre_topc(X1)=>((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&v2_tdlat_3(X1))=>((~(v2_struct_0(X1))&v7_struct_0(X1))&v2_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 2.54/2.70  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 2.54/2.70  fof(t34_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v2_tex_2(X2,X1)&![X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&v1_tdlat_3(X3))&m1_pre_topc(X3,X1))=>X2!=u1_struct_0(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 2.54/2.70  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.54/2.70  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.54/2.70  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 2.54/2.70  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.54/2.70  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.54/2.70  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 2.54/2.70  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.54/2.70  fof(c_0_18, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t44_tex_2])).
% 2.54/2.70  fof(c_0_19, plain, ![X26, X27, X28]:(~r2_hidden(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(X28))|m1_subset_1(X26,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 2.54/2.70  fof(c_0_20, negated_conjecture, ((((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&v2_tdlat_3(esk5_0))&l1_pre_topc(esk5_0))&((~v1_xboole_0(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&((~v2_tex_2(esk6_0,esk5_0)|~v1_zfmisc_1(esk6_0))&(v2_tex_2(esk6_0,esk5_0)|v1_zfmisc_1(esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 2.54/2.70  fof(c_0_21, plain, ![X38, X39]:(v2_struct_0(X38)|~v2_pre_topc(X38)|~v2_tdlat_3(X38)|~l1_pre_topc(X38)|(~m1_pre_topc(X39,X38)|v2_tdlat_3(X39))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).
% 2.54/2.70  fof(c_0_22, plain, ![X36]:(~l1_pre_topc(X36)|(~v2_tdlat_3(X36)|v2_pre_topc(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 2.54/2.70  cnf(c_0_23, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.54/2.70  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.54/2.70  fof(c_0_25, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 2.54/2.70  fof(c_0_26, plain, ![X22, X23]:(~v1_xboole_0(X22)|(~m1_subset_1(X23,k1_zfmisc_1(X22))|v1_xboole_0(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 2.54/2.70  fof(c_0_27, plain, ![X24, X25]:((~m1_subset_1(X24,k1_zfmisc_1(X25))|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|m1_subset_1(X24,k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 2.54/2.70  fof(c_0_28, plain, ![X20, X21]:(~r2_hidden(X20,X21)|m1_subset_1(k1_tarski(X20),k1_zfmisc_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 2.54/2.70  fof(c_0_29, plain, ![X37]:(((~v2_struct_0(X37)|(v2_struct_0(X37)|~v2_pre_topc(X37)|~v1_tdlat_3(X37)|~v2_tdlat_3(X37))|~l1_pre_topc(X37))&(v7_struct_0(X37)|(v2_struct_0(X37)|~v2_pre_topc(X37)|~v1_tdlat_3(X37)|~v2_tdlat_3(X37))|~l1_pre_topc(X37)))&(v2_pre_topc(X37)|(v2_struct_0(X37)|~v2_pre_topc(X37)|~v1_tdlat_3(X37)|~v2_tdlat_3(X37))|~l1_pre_topc(X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_1])])])])).
% 2.54/2.70  fof(c_0_30, plain, ![X35]:(~l1_pre_topc(X35)|(~v1_tdlat_3(X35)|v2_pre_topc(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 2.54/2.70  cnf(c_0_31, plain, (v2_struct_0(X1)|v2_tdlat_3(X2)|~v2_pre_topc(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.54/2.70  cnf(c_0_32, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.54/2.70  fof(c_0_33, plain, ![X42, X43]:(((((~v2_struct_0(esk4_2(X42,X43))|~v2_tex_2(X43,X42)|(v1_xboole_0(X43)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42))))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)))&(v1_pre_topc(esk4_2(X42,X43))|~v2_tex_2(X43,X42)|(v1_xboole_0(X43)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42))))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42))))&(v1_tdlat_3(esk4_2(X42,X43))|~v2_tex_2(X43,X42)|(v1_xboole_0(X43)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42))))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42))))&(m1_pre_topc(esk4_2(X42,X43),X42)|~v2_tex_2(X43,X42)|(v1_xboole_0(X43)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42))))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42))))&(X43=u1_struct_0(esk4_2(X42,X43))|~v2_tex_2(X43,X42)|(v1_xboole_0(X43)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42))))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).
% 2.54/2.70  fof(c_0_34, plain, ![X33, X34]:(v1_xboole_0(X33)|~m1_subset_1(X34,X33)|k6_domain_1(X33,X34)=k1_tarski(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 2.54/2.70  cnf(c_0_35, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 2.54/2.70  cnf(c_0_36, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.54/2.70  cnf(c_0_37, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.54/2.70  cnf(c_0_38, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.54/2.70  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.54/2.70  cnf(c_0_40, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.54/2.70  cnf(c_0_41, plain, (v7_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.54/2.70  cnf(c_0_42, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.54/2.70  cnf(c_0_43, plain, (v2_struct_0(X1)|v2_tdlat_3(X2)|~v2_tdlat_3(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_31, c_0_32])).
% 2.54/2.70  cnf(c_0_44, plain, (m1_pre_topc(esk4_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.54/2.70  fof(c_0_45, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|l1_pre_topc(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 2.54/2.70  fof(c_0_46, plain, ![X45, X46]:(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|(~m1_subset_1(X46,u1_struct_0(X45))|v2_tex_2(k6_domain_1(u1_struct_0(X45),X46),X45))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 2.54/2.70  cnf(c_0_47, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.54/2.70  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk1_1(esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 2.54/2.70  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_24]), c_0_37])).
% 2.54/2.70  fof(c_0_50, plain, ![X40, X41]:(v1_xboole_0(X40)|(v1_xboole_0(X41)|~v1_zfmisc_1(X41)|(~r1_tarski(X40,X41)|X40=X41))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 2.54/2.70  cnf(c_0_51, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 2.54/2.70  fof(c_0_52, plain, ![X17]:~v1_xboole_0(k1_tarski(X17)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 2.54/2.70  fof(c_0_53, plain, ![X32]:(~v7_struct_0(X32)|~l1_struct_0(X32)|v1_zfmisc_1(u1_struct_0(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 2.54/2.70  cnf(c_0_54, plain, (v2_struct_0(X1)|v7_struct_0(X1)|~v2_tdlat_3(X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_41, c_0_42])).
% 2.54/2.70  cnf(c_0_55, plain, (v2_struct_0(X1)|v2_tdlat_3(esk4_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_32])).
% 2.54/2.70  cnf(c_0_56, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.54/2.70  fof(c_0_57, plain, ![X29]:(~l1_pre_topc(X29)|l1_struct_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 2.54/2.70  cnf(c_0_58, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 2.54/2.70  cnf(c_0_59, negated_conjecture, (k6_domain_1(u1_struct_0(esk5_0),esk1_1(esk6_0))=k1_tarski(esk1_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 2.54/2.70  cnf(c_0_60, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.54/2.70  cnf(c_0_61, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.54/2.70  cnf(c_0_62, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.54/2.70  cnf(c_0_63, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.54/2.70  cnf(c_0_64, plain, (r1_tarski(k1_tarski(esk1_1(X1)),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_51, c_0_36])).
% 2.54/2.70  cnf(c_0_65, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 2.54/2.70  cnf(c_0_66, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 2.54/2.70  cnf(c_0_67, plain, (X1=u1_struct_0(esk4_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.54/2.70  cnf(c_0_68, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk4_2(X1,X2))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.54/2.70  cnf(c_0_69, plain, (v2_struct_0(esk4_2(X1,X2))|v2_struct_0(X1)|v7_struct_0(esk4_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~v1_tdlat_3(esk4_2(X1,X2))|~l1_pre_topc(esk4_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 2.54/2.70  cnf(c_0_70, plain, (v2_struct_0(X1)|l1_pre_topc(esk4_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_56, c_0_44])).
% 2.54/2.70  cnf(c_0_71, plain, (v1_tdlat_3(esk4_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.54/2.70  cnf(c_0_72, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 2.54/2.70  cnf(c_0_73, negated_conjecture, (v2_tex_2(k1_tarski(esk1_1(esk6_0)),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61]), c_0_48])]), c_0_62])).
% 2.54/2.70  cnf(c_0_74, plain, (k1_tarski(esk1_1(X1))=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 2.54/2.70  cnf(c_0_75, negated_conjecture, (v2_tex_2(esk6_0,esk5_0)|v1_zfmisc_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.54/2.70  cnf(c_0_76, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v7_struct_0(esk4_2(X1,X2))|~l1_struct_0(esk4_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 2.54/2.70  cnf(c_0_77, plain, (v2_struct_0(X1)|v7_struct_0(esk4_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71]), c_0_32])).
% 2.54/2.70  cnf(c_0_78, plain, (v2_struct_0(X1)|l1_struct_0(esk4_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_72, c_0_70])).
% 2.54/2.70  cnf(c_0_79, negated_conjecture, (~v2_tex_2(esk6_0,esk5_0)|~v1_zfmisc_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.54/2.70  cnf(c_0_80, negated_conjecture, (v2_tex_2(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_37]), c_0_75])).
% 2.54/2.70  cnf(c_0_81, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_32])).
% 2.54/2.70  cnf(c_0_82, negated_conjecture, (v2_tdlat_3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.54/2.70  cnf(c_0_83, negated_conjecture, (~v1_zfmisc_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 2.54/2.70  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_80]), c_0_82]), c_0_61]), c_0_24])]), c_0_62]), c_0_83]), c_0_37]), ['proof']).
% 2.54/2.70  # SZS output end CNFRefutation
% 2.54/2.70  # Proof object total steps             : 85
% 2.54/2.70  # Proof object clause steps            : 48
% 2.54/2.70  # Proof object formula steps           : 37
% 2.54/2.70  # Proof object conjectures             : 19
% 2.54/2.70  # Proof object clause conjectures      : 16
% 2.54/2.70  # Proof object formula conjectures     : 3
% 2.54/2.70  # Proof object initial clauses used    : 28
% 2.54/2.70  # Proof object initial formulas used   : 18
% 2.54/2.70  # Proof object generating inferences   : 17
% 2.54/2.70  # Proof object simplifying inferences  : 28
% 2.54/2.70  # Training examples: 0 positive, 0 negative
% 2.54/2.70  # Parsed axioms                        : 21
% 2.54/2.70  # Removed by relevancy pruning/SinE    : 0
% 2.54/2.70  # Initial clauses                      : 39
% 2.54/2.70  # Removed in clause preprocessing      : 2
% 2.54/2.70  # Initial clauses in saturation        : 37
% 2.54/2.70  # Processed clauses                    : 18176
% 2.54/2.70  # ...of these trivial                  : 194
% 2.54/2.70  # ...subsumed                          : 14829
% 2.54/2.70  # ...remaining for further processing  : 3153
% 2.54/2.70  # Other redundant clauses eliminated   : 0
% 2.54/2.70  # Clauses deleted for lack of memory   : 0
% 2.54/2.70  # Backward-subsumed                    : 114
% 2.54/2.70  # Backward-rewritten                   : 2
% 2.54/2.70  # Generated clauses                    : 205915
% 2.54/2.70  # ...of the previous two non-trivial   : 195797
% 2.54/2.70  # Contextual simplify-reflections      : 214
% 2.54/2.70  # Paramodulations                      : 205915
% 2.54/2.70  # Factorizations                       : 0
% 2.54/2.70  # Equation resolutions                 : 0
% 2.54/2.70  # Propositional unsat checks           : 0
% 2.54/2.70  #    Propositional check models        : 0
% 2.54/2.70  #    Propositional check unsatisfiable : 0
% 2.54/2.70  #    Propositional clauses             : 0
% 2.54/2.70  #    Propositional clauses after purity: 0
% 2.54/2.70  #    Propositional unsat core size     : 0
% 2.54/2.70  #    Propositional preprocessing time  : 0.000
% 2.54/2.70  #    Propositional encoding time       : 0.000
% 2.54/2.70  #    Propositional solver time         : 0.000
% 2.54/2.70  #    Success case prop preproc time    : 0.000
% 2.54/2.70  #    Success case prop encoding time   : 0.000
% 2.54/2.70  #    Success case prop solver time     : 0.000
% 2.54/2.70  # Current number of processed clauses  : 3000
% 2.54/2.70  #    Positive orientable unit clauses  : 288
% 2.54/2.70  #    Positive unorientable unit clauses: 0
% 2.54/2.70  #    Negative unit clauses             : 8
% 2.54/2.70  #    Non-unit-clauses                  : 2704
% 2.54/2.70  # Current number of unprocessed clauses: 177463
% 2.54/2.70  # ...number of literals in the above   : 777668
% 2.54/2.70  # Current number of archived formulas  : 0
% 2.54/2.70  # Current number of archived clauses   : 153
% 2.54/2.70  # Clause-clause subsumption calls (NU) : 3809258
% 2.54/2.70  # Rec. Clause-clause subsumption calls : 900516
% 2.54/2.70  # Non-unit clause-clause subsumptions  : 10998
% 2.54/2.70  # Unit Clause-clause subsumption calls : 23111
% 2.54/2.70  # Rewrite failures with RHS unbound    : 0
% 2.54/2.70  # BW rewrite match attempts            : 5894
% 2.54/2.70  # BW rewrite match successes           : 21
% 2.54/2.70  # Condensation attempts                : 0
% 2.54/2.70  # Condensation successes               : 0
% 2.54/2.70  # Termbank termtop insertions          : 4714397
% 2.54/2.71  
% 2.54/2.71  # -------------------------------------------------
% 2.54/2.71  # User time                : 2.291 s
% 2.54/2.71  # System time              : 0.082 s
% 2.54/2.71  # Total time               : 2.373 s
% 2.54/2.71  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
