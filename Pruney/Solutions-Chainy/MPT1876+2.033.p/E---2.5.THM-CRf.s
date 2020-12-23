%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:20 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 626 expanded)
%              Number of clauses        :   70 ( 221 expanded)
%              Number of leaves         :   22 ( 158 expanded)
%              Depth                    :   15
%              Number of atoms          :  448 (3922 expanded)
%              Number of equality atoms :   46 (  92 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t41_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r1_tarski(X3,X2)
                 => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(cc2_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_22,negated_conjecture,(
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

fof(c_0_23,plain,(
    ! [X43,X44] :
      ( ( ~ v2_struct_0(esk3_2(X43,X44))
        | ~ v2_tex_2(X44,X43)
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( v1_pre_topc(esk3_2(X43,X44))
        | ~ v2_tex_2(X44,X43)
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( v1_tdlat_3(esk3_2(X43,X44))
        | ~ v2_tex_2(X44,X43)
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( m1_pre_topc(esk3_2(X43,X44),X43)
        | ~ v2_tex_2(X44,X43)
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( X44 = u1_struct_0(esk3_2(X43,X44))
        | ~ v2_tex_2(X44,X43)
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

fof(c_0_24,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

fof(c_0_25,plain,(
    ! [X39,X40] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ v2_tdlat_3(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_pre_topc(X40,X39)
      | v2_tdlat_3(X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).

fof(c_0_26,plain,(
    ! [X37] :
      ( ~ l1_pre_topc(X37)
      | ~ v2_tdlat_3(X37)
      | v2_pre_topc(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

fof(c_0_27,plain,(
    ! [X38] :
      ( ( ~ v2_struct_0(X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ v1_tdlat_3(X38)
        | ~ v2_tdlat_3(X38)
        | ~ l1_pre_topc(X38) )
      & ( v7_struct_0(X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ v1_tdlat_3(X38)
        | ~ v2_tdlat_3(X38)
        | ~ l1_pre_topc(X38) )
      & ( v2_pre_topc(X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ v1_tdlat_3(X38)
        | ~ v2_tdlat_3(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_1])])])])).

fof(c_0_28,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | l1_pre_topc(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_29,plain,
    ( m1_pre_topc(esk3_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( v1_tdlat_3(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(esk3_2(esk5_0,esk6_0),esk5_0)
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])]),c_0_33]),c_0_34])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v2_tdlat_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk3_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_44,plain,(
    ! [X46,X47,X48] :
      ( ( ~ v2_tex_2(X47,X46)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X46)))
        | ~ r1_tarski(X48,X47)
        | k9_subset_1(u1_struct_0(X46),X47,k2_pre_topc(X46,X48)) = X48
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( m1_subset_1(esk4_2(X46,X47),k1_zfmisc_1(u1_struct_0(X46)))
        | v2_tex_2(X47,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( r1_tarski(esk4_2(X46,X47),X47)
        | v2_tex_2(X47,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( k9_subset_1(u1_struct_0(X46),X47,k2_pre_topc(X46,esk4_2(X46,X47))) != esk4_2(X46,X47)
        | v2_tex_2(X47,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).

fof(c_0_45,plain,(
    ! [X32] :
      ( ~ v7_struct_0(X32)
      | ~ l1_struct_0(X32)
      | v1_zfmisc_1(u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v1_tdlat_3(esk3_2(esk5_0,esk6_0))
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_31]),c_0_32])]),c_0_33]),c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( l1_pre_topc(esk3_2(esk5_0,esk6_0))
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_31])])).

cnf(c_0_49,negated_conjecture,
    ( v2_tdlat_3(esk3_2(esk5_0,esk6_0))
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_42]),c_0_31])]),c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_tex_2(esk6_0,esk5_0)
    | ~ v2_struct_0(esk3_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_30]),c_0_31]),c_0_32])]),c_0_33]),c_0_34])).

fof(c_0_51,plain,(
    ! [X41,X42] :
      ( v1_xboole_0(X41)
      | v1_xboole_0(X42)
      | ~ v1_zfmisc_1(X42)
      | ~ r1_tarski(X41,X42)
      | X41 = X42 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_52,plain,
    ( r1_tarski(esk4_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( v7_struct_0(esk3_2(esk5_0,esk6_0))
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_50])).

fof(c_0_55,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_56,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_57,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_58,plain,(
    ! [X16] :
      ( ~ v1_xboole_0(X16)
      | X16 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0)
    | r1_tarski(esk4_2(esk5_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0)
    | v1_zfmisc_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_62,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_2(esk5_0,esk6_0)))
    | ~ v2_tex_2(esk6_0,esk5_0)
    | ~ l1_struct_0(esk3_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( X1 = u1_struct_0(esk3_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_65,plain,(
    ! [X33,X34] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | r1_tarski(X34,k2_pre_topc(X33,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

fof(c_0_66,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_67,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( esk4_2(esk5_0,esk6_0) = esk6_0
    | v2_tex_2(esk6_0,esk5_0)
    | v1_xboole_0(esk4_2(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_34]),c_0_61])).

fof(c_0_71,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k9_subset_1(X22,X23,X24) = k3_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_72,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X19))
      | k9_subset_1(X19,X20,X21) = k9_subset_1(X19,X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_73,negated_conjecture,
    ( v1_zfmisc_1(u1_struct_0(esk3_2(esk5_0,esk6_0)))
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_48])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk3_2(esk5_0,esk6_0)) = esk6_0
    | ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_30]),c_0_31]),c_0_32])]),c_0_33]),c_0_34])).

cnf(c_0_75,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_76,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_79,plain,
    ( v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,esk4_2(X1,X2))) != esk4_2(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_80,negated_conjecture,
    ( esk4_2(esk5_0,esk6_0) = esk6_0
    | esk4_2(esk5_0,esk6_0) = k1_xboole_0
    | v2_tex_2(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_81,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_82,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_83,negated_conjecture,
    ( ~ v2_tex_2(esk6_0,esk5_0)
    | ~ v1_zfmisc_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_84,negated_conjecture,
    ( v1_zfmisc_1(esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_61])).

fof(c_0_85,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_87,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_88,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_89,plain,(
    ! [X35,X36] :
      ( ( ~ v4_pre_topc(X36,X35)
        | k2_pre_topc(X35,X36) = X36
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_pre_topc(X35) )
      & ( ~ v2_pre_topc(X35)
        | k2_pre_topc(X35,X36) != X36
        | v4_pre_topc(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_90,plain,(
    ! [X27,X28] :
      ( ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | ~ v1_xboole_0(X28)
      | v4_pre_topc(X28,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).

cnf(c_0_91,negated_conjecture,
    ( esk4_2(esk5_0,esk6_0) = k1_xboole_0
    | v2_tex_2(esk6_0,esk5_0)
    | k9_subset_1(u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk5_0,esk6_0)) != esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_31]),c_0_32]),c_0_30])]),c_0_33])).

cnf(c_0_92,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_93,negated_conjecture,
    ( ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_94,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_95,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k3_xboole_0(X17,X18) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_96,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(k2_pre_topc(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_86])).

cnf(c_0_97,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_98,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_99,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_100,negated_conjecture,
    ( esk4_2(esk5_0,esk6_0) = k1_xboole_0
    | k3_xboole_0(esk6_0,k2_pre_topc(esk5_0,esk6_0)) != esk6_0 ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_30])]),c_0_93]),c_0_94])).

cnf(c_0_101,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_102,plain,
    ( ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ v1_xboole_0(k2_pre_topc(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_103,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_87])).

cnf(c_0_104,negated_conjecture,
    ( esk4_2(esk5_0,esk6_0) = k1_xboole_0
    | ~ r1_tarski(esk6_0,k2_pre_topc(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_105,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_88])])).

cnf(c_0_106,plain,
    ( v2_tex_2(X1,X2)
    | v2_struct_0(X2)
    | k9_subset_1(u1_struct_0(X2),X1,esk4_2(X2,X1)) != esk4_2(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_xboole_0(esk4_2(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( esk4_2(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_76]),c_0_31]),c_0_30])])).

cnf(c_0_108,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_101])).

cnf(c_0_109,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_105,c_0_68])).

cnf(c_0_110,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk6_0,k1_xboole_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_31]),c_0_32]),c_0_30]),c_0_88])]),c_0_93]),c_0_33])).

cnf(c_0_111,plain,
    ( k9_subset_1(X1,X2,X3) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_31]),c_0_32])])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_97]),c_0_112])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:25:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.12/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.025 s
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t44_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 0.12/0.39  fof(t34_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v2_tex_2(X2,X1)&![X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&v1_tdlat_3(X3))&m1_pre_topc(X3,X1))=>X2!=u1_struct_0(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 0.12/0.39  fof(cc6_tdlat_3, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_tdlat_3(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 0.12/0.39  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 0.12/0.39  fof(cc2_tex_1, axiom, ![X1]:(l1_pre_topc(X1)=>((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&v2_tdlat_3(X1))=>((~(v2_struct_0(X1))&v7_struct_0(X1))&v2_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 0.12/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.12/0.39  fof(t41_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 0.12/0.39  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.12/0.39  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.12/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.12/0.39  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.12/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.39  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.12/0.39  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.12/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.12/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.39  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.18/0.39  fof(cc2_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 0.18/0.39  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.18/0.39  fof(c_0_22, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t44_tex_2])).
% 0.18/0.39  fof(c_0_23, plain, ![X43, X44]:(((((~v2_struct_0(esk3_2(X43,X44))|~v2_tex_2(X44,X43)|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)))&(v1_pre_topc(esk3_2(X43,X44))|~v2_tex_2(X44,X43)|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))&(v1_tdlat_3(esk3_2(X43,X44))|~v2_tex_2(X44,X43)|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))&(m1_pre_topc(esk3_2(X43,X44),X43)|~v2_tex_2(X44,X43)|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))&(X44=u1_struct_0(esk3_2(X43,X44))|~v2_tex_2(X44,X43)|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).
% 0.18/0.39  fof(c_0_24, negated_conjecture, ((((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&v2_tdlat_3(esk5_0))&l1_pre_topc(esk5_0))&((~v1_xboole_0(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&((~v2_tex_2(esk6_0,esk5_0)|~v1_zfmisc_1(esk6_0))&(v2_tex_2(esk6_0,esk5_0)|v1_zfmisc_1(esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.18/0.39  fof(c_0_25, plain, ![X39, X40]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~v2_tdlat_3(X39)|~l1_pre_topc(X39)|(~m1_pre_topc(X40,X39)|v2_tdlat_3(X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).
% 0.18/0.39  fof(c_0_26, plain, ![X37]:(~l1_pre_topc(X37)|(~v2_tdlat_3(X37)|v2_pre_topc(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 0.18/0.39  fof(c_0_27, plain, ![X38]:(((~v2_struct_0(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~v1_tdlat_3(X38)|~v2_tdlat_3(X38))|~l1_pre_topc(X38))&(v7_struct_0(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~v1_tdlat_3(X38)|~v2_tdlat_3(X38))|~l1_pre_topc(X38)))&(v2_pre_topc(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~v1_tdlat_3(X38)|~v2_tdlat_3(X38))|~l1_pre_topc(X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_1])])])])).
% 0.18/0.39  fof(c_0_28, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|l1_pre_topc(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.18/0.39  cnf(c_0_29, plain, (m1_pre_topc(esk3_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.39  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.39  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.39  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.39  cnf(c_0_34, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.39  cnf(c_0_35, plain, (v2_struct_0(X1)|v2_tdlat_3(X2)|~v2_pre_topc(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.39  cnf(c_0_36, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.39  cnf(c_0_37, plain, (v7_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.39  cnf(c_0_38, plain, (v1_tdlat_3(esk3_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  cnf(c_0_39, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.39  cnf(c_0_40, negated_conjecture, (m1_pre_topc(esk3_2(esk5_0,esk6_0),esk5_0)|~v2_tex_2(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])]), c_0_33]), c_0_34])).
% 0.18/0.39  cnf(c_0_41, plain, (v2_struct_0(X1)|v2_tdlat_3(X2)|~v2_tdlat_3(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.39  cnf(c_0_42, negated_conjecture, (v2_tdlat_3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.39  cnf(c_0_43, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk3_2(X1,X2))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  fof(c_0_44, plain, ![X46, X47, X48]:((~v2_tex_2(X47,X46)|(~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X46)))|(~r1_tarski(X48,X47)|k9_subset_1(u1_struct_0(X46),X47,k2_pre_topc(X46,X48))=X48))|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))&((m1_subset_1(esk4_2(X46,X47),k1_zfmisc_1(u1_struct_0(X46)))|v2_tex_2(X47,X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))&((r1_tarski(esk4_2(X46,X47),X47)|v2_tex_2(X47,X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))&(k9_subset_1(u1_struct_0(X46),X47,k2_pre_topc(X46,esk4_2(X46,X47)))!=esk4_2(X46,X47)|v2_tex_2(X47,X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).
% 0.18/0.39  fof(c_0_45, plain, ![X32]:(~v7_struct_0(X32)|~l1_struct_0(X32)|v1_zfmisc_1(u1_struct_0(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.18/0.39  cnf(c_0_46, plain, (v2_struct_0(X1)|v7_struct_0(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_37, c_0_36])).
% 0.18/0.39  cnf(c_0_47, negated_conjecture, (v1_tdlat_3(esk3_2(esk5_0,esk6_0))|~v2_tex_2(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_30]), c_0_31]), c_0_32])]), c_0_33]), c_0_34])).
% 0.18/0.39  cnf(c_0_48, negated_conjecture, (l1_pre_topc(esk3_2(esk5_0,esk6_0))|~v2_tex_2(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_31])])).
% 0.18/0.39  cnf(c_0_49, negated_conjecture, (v2_tdlat_3(esk3_2(esk5_0,esk6_0))|~v2_tex_2(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_42]), c_0_31])]), c_0_33])).
% 0.18/0.39  cnf(c_0_50, negated_conjecture, (~v2_tex_2(esk6_0,esk5_0)|~v2_struct_0(esk3_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_30]), c_0_31]), c_0_32])]), c_0_33]), c_0_34])).
% 0.18/0.39  fof(c_0_51, plain, ![X41, X42]:(v1_xboole_0(X41)|(v1_xboole_0(X42)|~v1_zfmisc_1(X42)|(~r1_tarski(X41,X42)|X41=X42))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.18/0.39  cnf(c_0_52, plain, (r1_tarski(esk4_2(X1,X2),X2)|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.39  cnf(c_0_53, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.39  cnf(c_0_54, negated_conjecture, (v7_struct_0(esk3_2(esk5_0,esk6_0))|~v2_tex_2(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 0.18/0.39  fof(c_0_55, plain, ![X29]:(~l1_pre_topc(X29)|l1_struct_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.39  fof(c_0_56, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.18/0.39  fof(c_0_57, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.39  fof(c_0_58, plain, ![X16]:(~v1_xboole_0(X16)|X16=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.18/0.39  cnf(c_0_59, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.18/0.39  cnf(c_0_60, negated_conjecture, (v2_tex_2(esk6_0,esk5_0)|r1_tarski(esk4_2(esk5_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_30]), c_0_31]), c_0_32])]), c_0_33])).
% 0.18/0.39  cnf(c_0_61, negated_conjecture, (v2_tex_2(esk6_0,esk5_0)|v1_zfmisc_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.39  cnf(c_0_62, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_2(esk5_0,esk6_0)))|~v2_tex_2(esk6_0,esk5_0)|~l1_struct_0(esk3_2(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.18/0.39  cnf(c_0_63, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.18/0.39  cnf(c_0_64, plain, (X1=u1_struct_0(esk3_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  fof(c_0_65, plain, ![X33, X34]:(~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|r1_tarski(X34,k2_pre_topc(X33,X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.18/0.39  fof(c_0_66, plain, ![X25, X26]:((~m1_subset_1(X25,k1_zfmisc_1(X26))|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|m1_subset_1(X25,k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.39  cnf(c_0_67, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.18/0.39  cnf(c_0_68, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.18/0.39  cnf(c_0_69, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.39  cnf(c_0_70, negated_conjecture, (esk4_2(esk5_0,esk6_0)=esk6_0|v2_tex_2(esk6_0,esk5_0)|v1_xboole_0(esk4_2(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_34]), c_0_61])).
% 0.18/0.39  fof(c_0_71, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(X22))|k9_subset_1(X22,X23,X24)=k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.18/0.39  fof(c_0_72, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(X19))|k9_subset_1(X19,X20,X21)=k9_subset_1(X19,X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.18/0.39  cnf(c_0_73, negated_conjecture, (v1_zfmisc_1(u1_struct_0(esk3_2(esk5_0,esk6_0)))|~v2_tex_2(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_48])).
% 0.18/0.39  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk3_2(esk5_0,esk6_0))=esk6_0|~v2_tex_2(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_30]), c_0_31]), c_0_32])]), c_0_33]), c_0_34])).
% 0.18/0.39  cnf(c_0_75, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.18/0.39  cnf(c_0_76, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.18/0.39  cnf(c_0_77, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.18/0.39  cnf(c_0_78, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.18/0.39  cnf(c_0_79, plain, (v2_tex_2(X2,X1)|v2_struct_0(X1)|k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,esk4_2(X1,X2)))!=esk4_2(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.39  cnf(c_0_80, negated_conjecture, (esk4_2(esk5_0,esk6_0)=esk6_0|esk4_2(esk5_0,esk6_0)=k1_xboole_0|v2_tex_2(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.18/0.39  cnf(c_0_81, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.18/0.39  cnf(c_0_82, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.18/0.39  cnf(c_0_83, negated_conjecture, (~v2_tex_2(esk6_0,esk5_0)|~v1_zfmisc_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.39  cnf(c_0_84, negated_conjecture, (v1_zfmisc_1(esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_61])).
% 0.18/0.39  fof(c_0_85, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.39  cnf(c_0_86, plain, (r2_hidden(X1,k2_pre_topc(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.18/0.39  cnf(c_0_87, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.18/0.39  cnf(c_0_88, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.39  fof(c_0_89, plain, ![X35, X36]:((~v4_pre_topc(X36,X35)|k2_pre_topc(X35,X36)=X36|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X35))&(~v2_pre_topc(X35)|k2_pre_topc(X35,X36)!=X36|v4_pre_topc(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.18/0.39  fof(c_0_90, plain, ![X27, X28]:(~v2_pre_topc(X27)|~l1_pre_topc(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(~v1_xboole_0(X28)|v4_pre_topc(X28,X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).
% 0.18/0.39  cnf(c_0_91, negated_conjecture, (esk4_2(esk5_0,esk6_0)=k1_xboole_0|v2_tex_2(esk6_0,esk5_0)|k9_subset_1(u1_struct_0(esk5_0),esk6_0,k2_pre_topc(esk5_0,esk6_0))!=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_31]), c_0_32]), c_0_30])]), c_0_33])).
% 0.18/0.39  cnf(c_0_92, plain, (k9_subset_1(X1,X2,X3)=k3_xboole_0(X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.18/0.39  cnf(c_0_93, negated_conjecture, (~v2_tex_2(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84])])).
% 0.18/0.39  cnf(c_0_94, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.18/0.39  fof(c_0_95, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k3_xboole_0(X17,X18)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.18/0.39  cnf(c_0_96, plain, (~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)|~v1_xboole_0(k2_pre_topc(X1,X2))), inference(spm,[status(thm)],[c_0_67, c_0_86])).
% 0.18/0.39  cnf(c_0_97, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.18/0.39  cnf(c_0_98, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.18/0.39  cnf(c_0_99, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.18/0.39  cnf(c_0_100, negated_conjecture, (esk4_2(esk5_0,esk6_0)=k1_xboole_0|k3_xboole_0(esk6_0,k2_pre_topc(esk5_0,esk6_0))!=esk6_0), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_30])]), c_0_93]), c_0_94])).
% 0.18/0.39  cnf(c_0_101, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.18/0.39  cnf(c_0_102, plain, (~l1_pre_topc(X1)|~r2_hidden(X2,k1_xboole_0)|~v1_xboole_0(k2_pre_topc(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.18/0.39  cnf(c_0_103, plain, (k2_pre_topc(X1,X2)=X2|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_87])).
% 0.18/0.39  cnf(c_0_104, negated_conjecture, (esk4_2(esk5_0,esk6_0)=k1_xboole_0|~r1_tarski(esk6_0,k2_pre_topc(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.18/0.39  cnf(c_0_105, plain, (~l1_pre_topc(X1)|~v2_pre_topc(X1)|~r2_hidden(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_88])])).
% 0.18/0.39  cnf(c_0_106, plain, (v2_tex_2(X1,X2)|v2_struct_0(X2)|k9_subset_1(u1_struct_0(X2),X1,esk4_2(X2,X1))!=esk4_2(X2,X1)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v1_xboole_0(esk4_2(X2,X1))), inference(spm,[status(thm)],[c_0_79, c_0_103])).
% 0.18/0.39  cnf(c_0_107, negated_conjecture, (esk4_2(esk5_0,esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_76]), c_0_31]), c_0_30])])).
% 0.18/0.39  cnf(c_0_108, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_94, c_0_101])).
% 0.18/0.39  cnf(c_0_109, plain, (r1_tarski(k1_xboole_0,X1)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_105, c_0_68])).
% 0.18/0.39  cnf(c_0_110, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk6_0,k1_xboole_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_31]), c_0_32]), c_0_30]), c_0_88])]), c_0_93]), c_0_33])).
% 0.18/0.39  cnf(c_0_111, plain, (k9_subset_1(X1,X2,X3)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_81, c_0_108])).
% 0.18/0.39  cnf(c_0_112, negated_conjecture, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_31]), c_0_32])])).
% 0.18/0.39  cnf(c_0_113, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_97]), c_0_112])]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 114
% 0.18/0.39  # Proof object clause steps            : 70
% 0.18/0.39  # Proof object formula steps           : 44
% 0.18/0.39  # Proof object conjectures             : 32
% 0.18/0.39  # Proof object clause conjectures      : 29
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 34
% 0.18/0.39  # Proof object initial formulas used   : 22
% 0.18/0.39  # Proof object generating inferences   : 33
% 0.18/0.39  # Proof object simplifying inferences  : 68
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 22
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 43
% 0.18/0.39  # Removed in clause preprocessing      : 2
% 0.18/0.39  # Initial clauses in saturation        : 41
% 0.18/0.39  # Processed clauses                    : 208
% 0.18/0.39  # ...of these trivial                  : 7
% 0.18/0.39  # ...subsumed                          : 53
% 0.18/0.39  # ...remaining for further processing  : 148
% 0.18/0.39  # Other redundant clauses eliminated   : 0
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 8
% 0.18/0.39  # Backward-rewritten                   : 13
% 0.18/0.39  # Generated clauses                    : 534
% 0.18/0.39  # ...of the previous two non-trivial   : 482
% 0.18/0.39  # Contextual simplify-reflections      : 18
% 0.18/0.39  # Paramodulations                      : 523
% 0.18/0.39  # Factorizations                       : 6
% 0.18/0.39  # Equation resolutions                 : 0
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 122
% 0.18/0.39  #    Positive orientable unit clauses  : 11
% 0.18/0.39  #    Positive unorientable unit clauses: 1
% 0.18/0.39  #    Negative unit clauses             : 8
% 0.18/0.39  #    Non-unit-clauses                  : 102
% 0.18/0.39  # Current number of unprocessed clauses: 292
% 0.18/0.39  # ...number of literals in the above   : 1426
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 26
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 3326
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 689
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 43
% 0.18/0.39  # Unit Clause-clause subsumption calls : 259
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 18
% 0.18/0.39  # BW rewrite match successes           : 5
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 13065
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.047 s
% 0.18/0.39  # System time              : 0.004 s
% 0.18/0.39  # Total time               : 0.051 s
% 0.18/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
