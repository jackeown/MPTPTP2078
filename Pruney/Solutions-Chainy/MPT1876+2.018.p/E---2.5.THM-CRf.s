%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:18 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 493 expanded)
%              Number of clauses        :   70 ( 191 expanded)
%              Number of leaves         :   24 ( 126 expanded)
%              Depth                    :   14
%              Number of atoms          :  518 (2885 expanded)
%              Number of equality atoms :   36 ( 101 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   35 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ! [X3] :
          ( m2_subset_1(X3,X1,X2)
        <=> m1_subset_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ? [X3] : m2_subset_1(X3,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_subset_1)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

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

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

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

fof(c_0_24,plain,(
    ! [X25,X26,X27] :
      ( ( ~ m2_subset_1(X27,X25,X26)
        | m1_subset_1(X27,X26)
        | v1_xboole_0(X25)
        | v1_xboole_0(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(X25)) )
      & ( ~ m1_subset_1(X27,X26)
        | m2_subset_1(X27,X25,X26)
        | v1_xboole_0(X25)
        | v1_xboole_0(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_m2_subset_1])])])])])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( ~ v1_xboole_0(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | v1_xboole_0(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_26,negated_conjecture,(
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

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m2_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])).

fof(c_0_30,plain,(
    ! [X32,X33,X34] :
      ( v2_struct_0(X32)
      | ~ l1_pre_topc(X32)
      | v2_struct_0(X33)
      | ~ m1_pre_topc(X33,X32)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | m1_subset_1(X34,u1_struct_0(X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

fof(c_0_31,plain,(
    ! [X41,X42] :
      ( ( ~ v2_struct_0(esk3_2(X41,X42))
        | v1_xboole_0(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ l1_pre_topc(X41) )
      & ( v1_pre_topc(esk3_2(X41,X42))
        | v1_xboole_0(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ l1_pre_topc(X41) )
      & ( m1_pre_topc(esk3_2(X41,X42),X41)
        | v1_xboole_0(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ l1_pre_topc(X41) )
      & ( X42 = u1_struct_0(esk3_2(X41,X42))
        | v1_xboole_0(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).

fof(c_0_32,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X20,X21)
      | v1_xboole_0(X21)
      | r2_hidden(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ m2_subset_1(X1,X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X22,X23] :
      ( v1_xboole_0(X22)
      | v1_xboole_0(X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | m2_subset_1(esk2_2(X22,X23),X22,X23) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_subset_1])])])])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( X1 = u1_struct_0(esk3_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk3_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_40,plain,(
    ! [X44,X45] :
      ( v1_xboole_0(X44)
      | v1_xboole_0(X45)
      | ~ v1_zfmisc_1(X45)
      | ~ r1_tarski(X44,X45)
      | X44 = X45 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

fof(c_0_41,plain,(
    ! [X10,X11] :
      ( ( ~ r1_tarski(k1_tarski(X10),X11)
        | r2_hidden(X10,X11) )
      & ( ~ r2_hidden(X10,X11)
        | r1_tarski(k1_tarski(X10),X11) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_42,plain,(
    ! [X9] : ~ v1_xboole_0(k1_tarski(X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_43,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(X1,esk6_0)
    | ~ m2_subset_1(X1,u1_struct_0(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m2_subset_1(esk2_2(X1,X2),X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X2))
    | v1_xboole_0(X4)
    | ~ m1_pre_topc(esk3_2(X1,X4),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_48,plain,
    ( m1_pre_topc(esk3_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ m2_subset_1(X1,u1_struct_0(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_35])).

cnf(c_0_54,plain,
    ( m2_subset_1(esk2_2(X1,X2),X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[c_0_46,c_0_28])).

fof(c_0_55,plain,(
    ! [X39,X40] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ v2_tdlat_3(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_pre_topc(X40,X39)
      | v2_tdlat_3(X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).

fof(c_0_56,plain,(
    ! [X37] :
      ( ~ l1_pre_topc(X37)
      | ~ v2_tdlat_3(X37)
      | v2_pre_topc(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X2,u1_struct_0(X1))
    | v1_xboole_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_60,plain,(
    ! [X18,X19] :
      ( ~ r2_hidden(X18,X19)
      | m1_subset_1(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_61,plain,(
    ! [X12,X13] :
      ( ( ~ r1_tarski(X12,k1_tarski(X13))
        | X12 = k1_xboole_0
        | X12 = k1_tarski(X13) )
      & ( X12 != k1_xboole_0
        | r1_tarski(X12,k1_tarski(X13)) )
      & ( X12 != k1_tarski(X13)
        | r1_tarski(X12,k1_tarski(X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_62,plain,
    ( k1_tarski(X1) = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk2_2(u1_struct_0(esk5_0),esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_34])]),c_0_35])).

fof(c_0_64,plain,(
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

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_67,plain,(
    ! [X46,X47] :
      ( ( ~ v2_struct_0(esk4_2(X46,X47))
        | ~ v2_tex_2(X47,X46)
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( v1_pre_topc(esk4_2(X46,X47))
        | ~ v2_tex_2(X47,X46)
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( v1_tdlat_3(esk4_2(X46,X47))
        | ~ v2_tex_2(X47,X46)
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( m1_pre_topc(esk4_2(X46,X47),X46)
        | ~ v2_tex_2(X47,X46)
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( X47 = u1_struct_0(esk4_2(X46,X47))
        | ~ v2_tex_2(X47,X46)
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_34]),c_0_58])]),c_0_59]),c_0_35])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( k1_tarski(esk2_2(u1_struct_0(esk5_0),esk6_0)) = esk6_0
    | ~ v1_zfmisc_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_72,plain,(
    ! [X14,X15] : k2_xboole_0(k1_tarski(X14),X15) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_73,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_74,plain,
    ( v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,plain,
    ( v2_tdlat_3(X1)
    | v2_struct_0(X2)
    | ~ v2_tdlat_3(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,plain,
    ( m1_pre_topc(esk4_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_77,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_pre_topc(X30,X29)
      | l1_pre_topc(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_78,plain,(
    ! [X35,X36] :
      ( v1_xboole_0(X35)
      | ~ m1_subset_1(X36,X35)
      | k6_domain_1(X35,X36) = k1_tarski(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_80,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_81,negated_conjecture,
    ( X1 = k1_xboole_0
    | X1 = esk6_0
    | ~ v1_zfmisc_1(esk6_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0)
    | v1_zfmisc_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_83,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_84,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_74,c_0_66])).

cnf(c_0_86,plain,
    ( v2_tdlat_3(esk4_2(X1,X2))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_66])).

cnf(c_0_87,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_88,plain,(
    ! [X49,X50] :
      ( v2_struct_0(X49)
      | ~ v2_pre_topc(X49)
      | ~ l1_pre_topc(X49)
      | ~ m1_subset_1(X50,u1_struct_0(X49))
      | v2_tex_2(k6_domain_1(u1_struct_0(X49),X50),X49) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_89,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk1_1(esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_35])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_34]),c_0_35])).

cnf(c_0_92,negated_conjecture,
    ( X1 = esk6_0
    | X1 = k1_xboole_0
    | v2_tex_2(esk6_0,esk5_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_93,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_94,plain,(
    ! [X31] :
      ( ~ v7_struct_0(X31)
      | ~ l1_struct_0(X31)
      | v1_zfmisc_1(u1_struct_0(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_95,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk4_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_96,plain,
    ( v2_struct_0(esk4_2(X1,X2))
    | v2_struct_0(X1)
    | v7_struct_0(esk4_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v1_tdlat_3(esk4_2(X1,X2))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(esk4_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_97,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(esk4_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_76])).

fof(c_0_98,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_99,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk5_0),esk1_1(esk6_0)) = k1_tarski(esk1_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

cnf(c_0_101,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_102,negated_conjecture,
    ( k1_tarski(X1) = esk6_0
    | v2_tex_2(esk6_0,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_50]),c_0_93])).

cnf(c_0_103,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_104,plain,
    ( X1 = u1_struct_0(esk4_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_105,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(esk4_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v1_tdlat_3(esk4_2(X1,X2))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97]),c_0_66])).

cnf(c_0_106,plain,
    ( v1_tdlat_3(esk4_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_107,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_108,negated_conjecture,
    ( v2_tex_2(k1_tarski(esk1_1(esk6_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101]),c_0_58]),c_0_90])]),c_0_59])).

cnf(c_0_109,negated_conjecture,
    ( k1_tarski(esk1_1(esk6_0)) = esk6_0
    | v2_tex_2(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_80]),c_0_35])).

cnf(c_0_110,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v7_struct_0(esk4_2(X1,X2))
    | ~ l1_struct_0(esk4_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_111,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(esk4_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_66])).

cnf(c_0_112,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(esk4_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_97])).

cnf(c_0_113,negated_conjecture,
    ( ~ v2_tex_2(esk6_0,esk5_0)
    | ~ v1_zfmisc_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_114,negated_conjecture,
    ( v2_tex_2(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_115,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112]),c_0_66])).

cnf(c_0_116,negated_conjecture,
    ( v2_tdlat_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_117,negated_conjecture,
    ( ~ v1_zfmisc_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114])])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_114]),c_0_116]),c_0_58]),c_0_34])]),c_0_59]),c_0_117]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.58  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.20/0.58  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.58  #
% 0.20/0.58  # Preprocessing time       : 0.029 s
% 0.20/0.58  # Presaturation interreduction done
% 0.20/0.58  
% 0.20/0.58  # Proof found!
% 0.20/0.58  # SZS status Theorem
% 0.20/0.58  # SZS output start CNFRefutation
% 0.20/0.58  fof(redefinition_m2_subset_1, axiom, ![X1, X2]:(((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(X1)))=>![X3]:(m2_subset_1(X3,X1,X2)<=>m1_subset_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_m2_subset_1)).
% 0.20/0.58  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.58  fof(t44_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 0.20/0.58  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.20/0.58  fof(t10_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>?[X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&X2=u1_struct_0(X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 0.20/0.58  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.58  fof(existence_m2_subset_1, axiom, ![X1, X2]:(((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(X1)))=>?[X3]:m2_subset_1(X3,X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_subset_1)).
% 0.20/0.58  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.20/0.58  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.20/0.58  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.20/0.58  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.58  fof(cc6_tdlat_3, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_tdlat_3(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 0.20/0.58  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 0.20/0.58  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.58  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.58  fof(cc2_tex_1, axiom, ![X1]:(l1_pre_topc(X1)=>((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&v2_tdlat_3(X1))=>((~(v2_struct_0(X1))&v7_struct_0(X1))&v2_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 0.20/0.58  fof(t34_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v2_tex_2(X2,X1)&![X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&v1_tdlat_3(X3))&m1_pre_topc(X3,X1))=>X2!=u1_struct_0(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 0.20/0.58  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.20/0.58  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.58  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.58  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.20/0.58  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 0.20/0.58  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.20/0.58  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.58  fof(c_0_24, plain, ![X25, X26, X27]:((~m2_subset_1(X27,X25,X26)|m1_subset_1(X27,X26)|(v1_xboole_0(X25)|v1_xboole_0(X26)|~m1_subset_1(X26,k1_zfmisc_1(X25))))&(~m1_subset_1(X27,X26)|m2_subset_1(X27,X25,X26)|(v1_xboole_0(X25)|v1_xboole_0(X26)|~m1_subset_1(X26,k1_zfmisc_1(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_m2_subset_1])])])])])).
% 0.20/0.58  fof(c_0_25, plain, ![X16, X17]:(~v1_xboole_0(X16)|(~m1_subset_1(X17,k1_zfmisc_1(X16))|v1_xboole_0(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.58  fof(c_0_26, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t44_tex_2])).
% 0.20/0.58  cnf(c_0_27, plain, (m1_subset_1(X1,X3)|v1_xboole_0(X2)|v1_xboole_0(X3)|~m2_subset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.58  cnf(c_0_28, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.58  fof(c_0_29, negated_conjecture, ((((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&v2_tdlat_3(esk5_0))&l1_pre_topc(esk5_0))&((~v1_xboole_0(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&((~v2_tex_2(esk6_0,esk5_0)|~v1_zfmisc_1(esk6_0))&(v2_tex_2(esk6_0,esk5_0)|v1_zfmisc_1(esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])).
% 0.20/0.58  fof(c_0_30, plain, ![X32, X33, X34]:(v2_struct_0(X32)|~l1_pre_topc(X32)|(v2_struct_0(X33)|~m1_pre_topc(X33,X32)|(~m1_subset_1(X34,u1_struct_0(X33))|m1_subset_1(X34,u1_struct_0(X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.20/0.58  fof(c_0_31, plain, ![X41, X42]:((((~v2_struct_0(esk3_2(X41,X42))|(v1_xboole_0(X42)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))))|(v2_struct_0(X41)|~l1_pre_topc(X41)))&(v1_pre_topc(esk3_2(X41,X42))|(v1_xboole_0(X42)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))))|(v2_struct_0(X41)|~l1_pre_topc(X41))))&(m1_pre_topc(esk3_2(X41,X42),X41)|(v1_xboole_0(X42)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))))|(v2_struct_0(X41)|~l1_pre_topc(X41))))&(X42=u1_struct_0(esk3_2(X41,X42))|(v1_xboole_0(X42)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))))|(v2_struct_0(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).
% 0.20/0.58  fof(c_0_32, plain, ![X20, X21]:(~m1_subset_1(X20,X21)|(v1_xboole_0(X21)|r2_hidden(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.58  cnf(c_0_33, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~m2_subset_1(X1,X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.58  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.58  cnf(c_0_35, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.58  fof(c_0_36, plain, ![X22, X23]:(v1_xboole_0(X22)|v1_xboole_0(X23)|~m1_subset_1(X23,k1_zfmisc_1(X22))|m2_subset_1(esk2_2(X22,X23),X22,X23)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_subset_1])])])])).
% 0.20/0.58  cnf(c_0_37, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.58  cnf(c_0_38, plain, (X1=u1_struct_0(esk3_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.58  cnf(c_0_39, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk3_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.58  fof(c_0_40, plain, ![X44, X45]:(v1_xboole_0(X44)|(v1_xboole_0(X45)|~v1_zfmisc_1(X45)|(~r1_tarski(X44,X45)|X44=X45))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.20/0.58  fof(c_0_41, plain, ![X10, X11]:((~r1_tarski(k1_tarski(X10),X11)|r2_hidden(X10,X11))&(~r2_hidden(X10,X11)|r1_tarski(k1_tarski(X10),X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.20/0.58  fof(c_0_42, plain, ![X9]:~v1_xboole_0(k1_tarski(X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.20/0.58  fof(c_0_43, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.58  cnf(c_0_44, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.58  cnf(c_0_45, negated_conjecture, (m1_subset_1(X1,esk6_0)|~m2_subset_1(X1,u1_struct_0(esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.20/0.58  cnf(c_0_46, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m2_subset_1(esk2_2(X1,X2),X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.58  cnf(c_0_47, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X2))|v1_xboole_0(X4)|~m1_pre_topc(esk3_2(X1,X4),X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.20/0.58  cnf(c_0_48, plain, (m1_pre_topc(esk3_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.58  cnf(c_0_49, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.58  cnf(c_0_50, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.58  cnf(c_0_51, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.58  cnf(c_0_52, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.58  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,esk6_0)|~m2_subset_1(X1,u1_struct_0(esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_35])).
% 0.20/0.58  cnf(c_0_54, plain, (m2_subset_1(esk2_2(X1,X2),X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_46, c_0_28])).
% 0.20/0.58  fof(c_0_55, plain, ![X39, X40]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~v2_tdlat_3(X39)|~l1_pre_topc(X39)|(~m1_pre_topc(X40,X39)|v2_tdlat_3(X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).
% 0.20/0.58  fof(c_0_56, plain, ![X37]:(~l1_pre_topc(X37)|(~v2_tdlat_3(X37)|v2_pre_topc(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 0.20/0.58  cnf(c_0_57, plain, (v2_struct_0(X1)|m1_subset_1(X2,u1_struct_0(X1))|v1_xboole_0(X3)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,X3)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.58  cnf(c_0_58, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.58  cnf(c_0_59, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.58  fof(c_0_60, plain, ![X18, X19]:(~r2_hidden(X18,X19)|m1_subset_1(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.58  fof(c_0_61, plain, ![X12, X13]:((~r1_tarski(X12,k1_tarski(X13))|(X12=k1_xboole_0|X12=k1_tarski(X13)))&((X12!=k1_xboole_0|r1_tarski(X12,k1_tarski(X13)))&(X12!=k1_tarski(X13)|r1_tarski(X12,k1_tarski(X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.58  cnf(c_0_62, plain, (k1_tarski(X1)=X2|~v1_zfmisc_1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52])).
% 0.20/0.58  cnf(c_0_63, negated_conjecture, (r2_hidden(esk2_2(u1_struct_0(esk5_0),esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_34])]), c_0_35])).
% 0.20/0.58  fof(c_0_64, plain, ![X38]:(((~v2_struct_0(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~v1_tdlat_3(X38)|~v2_tdlat_3(X38))|~l1_pre_topc(X38))&(v7_struct_0(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~v1_tdlat_3(X38)|~v2_tdlat_3(X38))|~l1_pre_topc(X38)))&(v2_pre_topc(X38)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~v1_tdlat_3(X38)|~v2_tdlat_3(X38))|~l1_pre_topc(X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_1])])])])).
% 0.20/0.58  cnf(c_0_65, plain, (v2_struct_0(X1)|v2_tdlat_3(X2)|~v2_pre_topc(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.58  cnf(c_0_66, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.58  fof(c_0_67, plain, ![X46, X47]:(((((~v2_struct_0(esk4_2(X46,X47))|~v2_tex_2(X47,X46)|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46))))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))&(v1_pre_topc(esk4_2(X46,X47))|~v2_tex_2(X47,X46)|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46))))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))))&(v1_tdlat_3(esk4_2(X46,X47))|~v2_tex_2(X47,X46)|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46))))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))))&(m1_pre_topc(esk4_2(X46,X47),X46)|~v2_tex_2(X47,X46)|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46))))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))))&(X47=u1_struct_0(esk4_2(X46,X47))|~v2_tex_2(X47,X46)|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46))))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).
% 0.20/0.58  cnf(c_0_68, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_34]), c_0_58])]), c_0_59]), c_0_35])).
% 0.20/0.58  cnf(c_0_69, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.58  cnf(c_0_70, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.58  cnf(c_0_71, negated_conjecture, (k1_tarski(esk2_2(u1_struct_0(esk5_0),esk6_0))=esk6_0|~v1_zfmisc_1(esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.58  fof(c_0_72, plain, ![X14, X15]:k2_xboole_0(k1_tarski(X14),X15)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.20/0.58  fof(c_0_73, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.58  cnf(c_0_74, plain, (v7_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.58  cnf(c_0_75, plain, (v2_tdlat_3(X1)|v2_struct_0(X2)|~v2_tdlat_3(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.58  cnf(c_0_76, plain, (m1_pre_topc(esk4_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.58  fof(c_0_77, plain, ![X29, X30]:(~l1_pre_topc(X29)|(~m1_pre_topc(X30,X29)|l1_pre_topc(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.58  fof(c_0_78, plain, ![X35, X36]:(v1_xboole_0(X35)|~m1_subset_1(X36,X35)|k6_domain_1(X35,X36)=k1_tarski(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.20/0.58  cnf(c_0_79, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.58  cnf(c_0_80, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.58  cnf(c_0_81, negated_conjecture, (X1=k1_xboole_0|X1=esk6_0|~v1_zfmisc_1(esk6_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.58  cnf(c_0_82, negated_conjecture, (v2_tex_2(esk6_0,esk5_0)|v1_zfmisc_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.58  cnf(c_0_83, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.58  cnf(c_0_84, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.58  cnf(c_0_85, plain, (v2_struct_0(X1)|v7_struct_0(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_74, c_0_66])).
% 0.20/0.58  cnf(c_0_86, plain, (v2_tdlat_3(esk4_2(X1,X2))|v2_struct_0(X1)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_66])).
% 0.20/0.58  cnf(c_0_87, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.58  fof(c_0_88, plain, ![X49, X50]:(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)|(~m1_subset_1(X50,u1_struct_0(X49))|v2_tex_2(k6_domain_1(u1_struct_0(X49),X50),X49))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 0.20/0.58  cnf(c_0_89, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.58  cnf(c_0_90, negated_conjecture, (m1_subset_1(esk1_1(esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_35])).
% 0.20/0.58  cnf(c_0_91, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_34]), c_0_35])).
% 0.20/0.58  cnf(c_0_92, negated_conjecture, (X1=esk6_0|X1=k1_xboole_0|v2_tex_2(esk6_0,esk5_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.58  cnf(c_0_93, plain, (k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.58  fof(c_0_94, plain, ![X31]:(~v7_struct_0(X31)|~l1_struct_0(X31)|v1_zfmisc_1(u1_struct_0(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.20/0.58  cnf(c_0_95, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk4_2(X1,X2))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.58  cnf(c_0_96, plain, (v2_struct_0(esk4_2(X1,X2))|v2_struct_0(X1)|v7_struct_0(esk4_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v1_tdlat_3(esk4_2(X1,X2))|~v2_tdlat_3(X1)|~l1_pre_topc(esk4_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.20/0.58  cnf(c_0_97, plain, (v2_struct_0(X1)|l1_pre_topc(esk4_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_87, c_0_76])).
% 0.20/0.58  fof(c_0_98, plain, ![X28]:(~l1_pre_topc(X28)|l1_struct_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.58  cnf(c_0_99, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.58  cnf(c_0_100, negated_conjecture, (k6_domain_1(u1_struct_0(esk5_0),esk1_1(esk6_0))=k1_tarski(esk1_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])).
% 0.20/0.58  cnf(c_0_101, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.58  cnf(c_0_102, negated_conjecture, (k1_tarski(X1)=esk6_0|v2_tex_2(esk6_0,esk5_0)|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_50]), c_0_93])).
% 0.20/0.58  cnf(c_0_103, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.20/0.58  cnf(c_0_104, plain, (X1=u1_struct_0(esk4_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.58  cnf(c_0_105, plain, (v2_struct_0(X1)|v7_struct_0(esk4_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v1_tdlat_3(esk4_2(X1,X2))|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97]), c_0_66])).
% 0.20/0.58  cnf(c_0_106, plain, (v1_tdlat_3(esk4_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.58  cnf(c_0_107, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.20/0.58  cnf(c_0_108, negated_conjecture, (v2_tex_2(k1_tarski(esk1_1(esk6_0)),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101]), c_0_58]), c_0_90])]), c_0_59])).
% 0.20/0.58  cnf(c_0_109, negated_conjecture, (k1_tarski(esk1_1(esk6_0))=esk6_0|v2_tex_2(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_80]), c_0_35])).
% 0.20/0.58  cnf(c_0_110, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v7_struct_0(esk4_2(X1,X2))|~l1_struct_0(esk4_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.20/0.58  cnf(c_0_111, plain, (v2_struct_0(X1)|v7_struct_0(esk4_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_66])).
% 0.20/0.58  cnf(c_0_112, plain, (v2_struct_0(X1)|l1_struct_0(esk4_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_107, c_0_97])).
% 0.20/0.58  cnf(c_0_113, negated_conjecture, (~v2_tex_2(esk6_0,esk5_0)|~v1_zfmisc_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.58  cnf(c_0_114, negated_conjecture, (v2_tex_2(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.20/0.58  cnf(c_0_115, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112]), c_0_66])).
% 0.20/0.58  cnf(c_0_116, negated_conjecture, (v2_tdlat_3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.58  cnf(c_0_117, negated_conjecture, (~v1_zfmisc_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_114])])).
% 0.20/0.58  cnf(c_0_118, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_114]), c_0_116]), c_0_58]), c_0_34])]), c_0_59]), c_0_117]), c_0_35]), ['proof']).
% 0.20/0.58  # SZS output end CNFRefutation
% 0.20/0.58  # Proof object total steps             : 119
% 0.20/0.58  # Proof object clause steps            : 70
% 0.20/0.58  # Proof object formula steps           : 49
% 0.20/0.58  # Proof object conjectures             : 28
% 0.20/0.58  # Proof object clause conjectures      : 25
% 0.20/0.58  # Proof object formula conjectures     : 3
% 0.20/0.58  # Proof object initial clauses used    : 37
% 0.20/0.58  # Proof object initial formulas used   : 24
% 0.20/0.58  # Proof object generating inferences   : 28
% 0.20/0.58  # Proof object simplifying inferences  : 41
% 0.20/0.58  # Training examples: 0 positive, 0 negative
% 0.20/0.58  # Parsed axioms                        : 24
% 0.20/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.58  # Initial clauses                      : 45
% 0.20/0.58  # Removed in clause preprocessing      : 2
% 0.20/0.58  # Initial clauses in saturation        : 43
% 0.20/0.58  # Processed clauses                    : 2507
% 0.20/0.58  # ...of these trivial                  : 7
% 0.20/0.58  # ...subsumed                          : 1793
% 0.20/0.58  # ...remaining for further processing  : 707
% 0.20/0.58  # Other redundant clauses eliminated   : 4
% 0.20/0.58  # Clauses deleted for lack of memory   : 0
% 0.20/0.58  # Backward-subsumed                    : 30
% 0.20/0.58  # Backward-rewritten                   : 11
% 0.20/0.58  # Generated clauses                    : 4552
% 0.20/0.58  # ...of the previous two non-trivial   : 4054
% 0.20/0.58  # Contextual simplify-reflections      : 100
% 0.20/0.58  # Paramodulations                      : 4548
% 0.20/0.58  # Factorizations                       : 0
% 0.20/0.58  # Equation resolutions                 : 4
% 0.20/0.58  # Propositional unsat checks           : 0
% 0.20/0.58  #    Propositional check models        : 0
% 0.20/0.58  #    Propositional check unsatisfiable : 0
% 0.20/0.58  #    Propositional clauses             : 0
% 0.20/0.58  #    Propositional clauses after purity: 0
% 0.20/0.58  #    Propositional unsat core size     : 0
% 0.20/0.58  #    Propositional preprocessing time  : 0.000
% 0.20/0.58  #    Propositional encoding time       : 0.000
% 0.20/0.58  #    Propositional solver time         : 0.000
% 0.20/0.58  #    Success case prop preproc time    : 0.000
% 0.20/0.58  #    Success case prop encoding time   : 0.000
% 0.20/0.58  #    Success case prop solver time     : 0.000
% 0.20/0.58  # Current number of processed clauses  : 621
% 0.20/0.58  #    Positive orientable unit clauses  : 31
% 0.20/0.58  #    Positive unorientable unit clauses: 0
% 0.20/0.58  #    Negative unit clauses             : 7
% 0.20/0.58  #    Non-unit-clauses                  : 583
% 0.20/0.58  # Current number of unprocessed clauses: 1607
% 0.20/0.58  # ...number of literals in the above   : 12675
% 0.20/0.58  # Current number of archived formulas  : 0
% 0.20/0.58  # Current number of archived clauses   : 84
% 0.20/0.58  # Clause-clause subsumption calls (NU) : 160336
% 0.20/0.58  # Rec. Clause-clause subsumption calls : 25526
% 0.20/0.58  # Non-unit clause-clause subsumptions  : 1590
% 0.20/0.58  # Unit Clause-clause subsumption calls : 305
% 0.20/0.58  # Rewrite failures with RHS unbound    : 0
% 0.20/0.58  # BW rewrite match attempts            : 8
% 0.20/0.58  # BW rewrite match successes           : 3
% 0.20/0.58  # Condensation attempts                : 0
% 0.20/0.58  # Condensation successes               : 0
% 0.20/0.58  # Termbank termtop insertions          : 108130
% 0.20/0.58  
% 0.20/0.58  # -------------------------------------------------
% 0.20/0.58  # User time                : 0.224 s
% 0.20/0.58  # System time              : 0.011 s
% 0.20/0.58  # Total time               : 0.235 s
% 0.20/0.58  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
