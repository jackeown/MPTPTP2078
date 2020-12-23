%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1887+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:59 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  156 (1805 expanded)
%              Number of clauses        :  116 ( 763 expanded)
%              Number of leaves         :   20 ( 458 expanded)
%              Depth                    :   43
%              Number of atoms          :  595 (7491 expanded)
%              Number of equality atoms :  108 ( 661 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t40_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r1_xboole_0(X2,X3)
                  & v3_pre_topc(X2,X1) )
               => r1_xboole_0(X2,k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t31_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v4_pre_topc(X2,X1)
                  & r1_tarski(X3,X2) )
               => r1_tarski(k2_pre_topc(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(t24_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t56_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(t55_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
               => k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_20,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_21,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k3_xboole_0(X21,X22) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_22,plain,(
    ! [X16,X17] :
      ( ~ r1_xboole_0(X16,X17)
      | r1_xboole_0(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_23,plain,(
    ! [X32,X33,X34] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ r1_xboole_0(X33,X34)
      | ~ v3_pre_topc(X33,X32)
      | r1_xboole_0(X33,k2_pre_topc(X32,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_tsep_1])])])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X2,k2_pre_topc(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X2,X3)
    | ~ v3_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k2_pre_topc(X1,X2),X3)
    | ~ v3_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_30,plain,(
    ! [X30,X31] :
      ( ( ~ m1_subset_1(X30,k1_zfmisc_1(X31))
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(X30,X31)
        | m1_subset_1(X30,k1_zfmisc_1(X31)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_31,plain,(
    ! [X25,X26,X27] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ v4_pre_topc(X26,X25)
      | ~ r1_tarski(X27,X26)
      | r1_tarski(k2_pre_topc(X25,X27),X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).

cnf(c_0_32,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_tarski(k2_pre_topc(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_34,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
      | m1_subset_1(k2_pre_topc(X8,X9),k1_zfmisc_1(u1_struct_0(X8))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_pre_topc(X1,X3),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_tarski(k2_pre_topc(X1,X2),X3)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_38,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | r1_tarski(X36,k2_pre_topc(X35,X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),X3)
    | ~ v4_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_40,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_pre_topc(k2_pre_topc(X1,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(k2_pre_topc(X1,X3),X2)
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ v4_pre_topc(k2_pre_topc(X1,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

fof(c_0_43,plain,(
    ! [X11,X12] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | v4_pre_topc(k2_pre_topc(X11,X12),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_44,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_pre_topc(k2_pre_topc(X1,k2_pre_topc(X1,X2)),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(k2_pre_topc(X1,k2_pre_topc(X1,X2)),X2)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_46,plain,(
    ! [X18,X19] :
      ( ( ~ v3_tdlat_3(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v4_pre_topc(X19,X18)
        | v3_pre_topc(X19,X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk1_1(X18),k1_zfmisc_1(u1_struct_0(X18)))
        | v3_tdlat_3(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( v4_pre_topc(esk1_1(X18),X18)
        | v3_tdlat_3(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ v3_pre_topc(esk1_1(X18),X18)
        | v3_tdlat_3(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

fof(c_0_47,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_48,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ v4_pre_topc(k2_pre_topc(X1,X3),X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ r1_tarski(X2,u1_struct_0(X1))
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_33])).

cnf(c_0_49,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_pre_topc(k2_pre_topc(X1,k2_pre_topc(X1,X2)),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(k2_pre_topc(X1,k2_pre_topc(X1,X2)),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_37]),c_0_45])).

cnf(c_0_51,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_45])).

cnf(c_0_54,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_tdlat_3(X1)
    | ~ v4_pre_topc(k2_pre_topc(X1,k2_pre_topc(X1,X2)),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k2_pre_topc(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(k2_pre_topc(X1,k2_pre_topc(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_55,plain,(
    ! [X37,X38] :
      ( r2_hidden(X37,X38)
      | r1_xboole_0(k1_tarski(X37),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_zfmisc_1])])])).

fof(c_0_56,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
                 => k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t55_tex_2])).

cnf(c_0_57,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ r1_tarski(X3,k2_pre_topc(X1,X2))
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_tdlat_3(X1)
    | ~ v4_pre_topc(k2_pre_topc(X1,k2_pre_topc(X1,X2)),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(k2_pre_topc(X1,k2_pre_topc(X1,X2)),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_37]),c_0_37])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_60,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & v3_tdlat_3(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & r2_hidden(esk3_0,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))
    & k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) != k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_56])])])])).

fof(c_0_61,plain,(
    ! [X13] :
      ( v2_struct_0(X13)
      | ~ l1_struct_0(X13)
      | ~ v1_xboole_0(u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_62,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X3,k2_pre_topc(X1,X2))
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_53]),c_0_45]),c_0_45])).

cnf(c_0_63,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(k2_pre_topc(X1,k2_pre_topc(X1,X2)),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_49]),c_0_37])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(X2,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_67,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(X10)
      | l1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_68,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X3,k2_pre_topc(X1,X2))
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_33])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_70,plain,
    ( k2_pre_topc(X1,k1_tarski(X2)) = k1_xboole_0
    | r2_hidden(X2,k2_pre_topc(X1,k2_pre_topc(X1,k1_tarski(X2))))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k1_tarski(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_71,plain,(
    ! [X28,X29] :
      ( ( ~ r1_tarski(k1_tarski(X28),X29)
        | r2_hidden(X28,X29) )
      & ( ~ r2_hidden(X28,X29)
        | r1_tarski(k1_tarski(X28),X29) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

fof(c_0_72,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_76,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X3,k2_pre_topc(X1,X2))
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ r1_tarski(X2,u1_struct_0(X1))
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_33])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( k2_pre_topc(X1,k1_tarski(X2)) = k1_xboole_0
    | r2_hidden(X2,k2_pre_topc(X1,k2_pre_topc(X1,k1_tarski(X2))))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k1_tarski(X2),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_33])).

cnf(c_0_79,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

cnf(c_0_83,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k2_pre_topc(X1,k2_pre_topc(X1,X2)))
    | ~ r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,plain,
    ( k2_pre_topc(X1,k1_tarski(X2)) = k1_xboole_0
    | r2_hidden(X2,k2_pre_topc(X1,k2_pre_topc(X1,k1_tarski(X2))))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( v3_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_87,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_88,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,k1_tarski(X2))) = k2_pre_topc(X1,k1_tarski(X2))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k2_pre_topc(X1,k1_tarski(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_pre_topc(X1,k1_tarski(X2)),u1_struct_0(X1))
    | ~ r1_tarski(k1_tarski(X2),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_87]),c_0_75])])).

cnf(c_0_90,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk4_0))) = k2_pre_topc(esk2_0,k1_tarski(esk4_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | ~ r1_tarski(k2_pre_topc(esk2_0,k1_tarski(esk4_0)),u1_struct_0(esk2_0))
    | ~ r1_tarski(k1_tarski(esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_87]),c_0_75])])).

cnf(c_0_91,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk4_0))) = k2_pre_topc(esk2_0,k1_tarski(esk4_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | ~ r1_tarski(k2_pre_topc(esk2_0,k1_tarski(esk4_0)),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_79]),c_0_85])])).

cnf(c_0_92,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_93,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk4_0))) = k2_pre_topc(esk2_0,k1_tarski(esk4_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | ~ m1_subset_1(k1_tarski(esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_75])])).

cnf(c_0_94,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk4_0))) = k2_pre_topc(esk2_0,k1_tarski(esk4_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | ~ r1_tarski(k1_tarski(esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_33])).

cnf(c_0_95,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk4_0))) = k2_pre_topc(esk2_0,k1_tarski(esk4_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_79]),c_0_85])])).

cnf(c_0_96,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | v4_pre_topc(k2_pre_topc(esk2_0,k1_tarski(esk4_0)),esk2_0)
    | ~ m1_subset_1(k2_pre_topc(esk2_0,k1_tarski(esk4_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_95]),c_0_87]),c_0_75])])).

cnf(c_0_97,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | v4_pre_topc(k2_pre_topc(esk2_0,k1_tarski(esk4_0)),esk2_0)
    | ~ m1_subset_1(k1_tarski(esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_37]),c_0_75])])).

cnf(c_0_98,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | v4_pre_topc(k2_pre_topc(esk2_0,k1_tarski(esk4_0)),esk2_0)
    | ~ r1_tarski(k1_tarski(esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_33])).

cnf(c_0_99,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | v4_pre_topc(k2_pre_topc(esk2_0,k1_tarski(esk4_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_79]),c_0_85])])).

fof(c_0_100,plain,(
    ! [X14,X15] :
      ( v1_xboole_0(X14)
      | ~ m1_subset_1(X15,X14)
      | k6_domain_1(X14,X15) = k1_tarski(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_101,plain,
    ( X1 = k1_xboole_0
    | ~ v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k2_pre_topc(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_103,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | r1_tarski(k2_pre_topc(esk2_0,X1),k2_pre_topc(esk2_0,k1_tarski(esk4_0)))
    | ~ r1_tarski(X1,k2_pre_topc(esk2_0,k1_tarski(esk4_0)))
    | ~ r1_tarski(k1_tarski(esk4_0),u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_99]),c_0_75])])).

cnf(c_0_104,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_105,plain,
    ( X1 = k1_xboole_0
    | ~ v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_33])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_102]),c_0_82])).

cnf(c_0_107,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | r1_tarski(k2_pre_topc(esk2_0,X1),k2_pre_topc(esk2_0,k1_tarski(esk4_0)))
    | ~ r1_tarski(X1,k2_pre_topc(esk2_0,k1_tarski(esk4_0)))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_79]),c_0_85])])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(esk3_0,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_109,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk4_0) = k1_tarski(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_81]),c_0_82])).

cnf(c_0_110,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(k2_pre_topc(X1,X2),X3)
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_37])).

cnf(c_0_111,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | r2_hidden(esk3_0,k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_106]),c_0_86]),c_0_87]),c_0_75])])).

cnf(c_0_112,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | r1_tarski(k2_pre_topc(esk2_0,k1_tarski(X1)),k2_pre_topc(esk2_0,k1_tarski(esk4_0)))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,k1_tarski(esk4_0)))
    | ~ r1_tarski(k1_tarski(X1),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_79])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(esk3_0,k2_pre_topc(esk2_0,k1_tarski(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_114,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(k2_pre_topc(X1,X2),X3)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_53]),c_0_45]),c_0_45])).

cnf(c_0_115,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))) = k2_pre_topc(esk2_0,k1_tarski(esk3_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | ~ r1_tarski(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),u1_struct_0(esk2_0))
    | ~ r1_tarski(k1_tarski(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_111]),c_0_87]),c_0_75])])).

cnf(c_0_116,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | r1_tarski(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),k2_pre_topc(esk2_0,k1_tarski(esk4_0)))
    | ~ r1_tarski(k1_tarski(esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_117,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(k2_pre_topc(X1,X2),X3)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_33])).

cnf(c_0_118,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))) = k2_pre_topc(esk2_0,k1_tarski(esk3_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | ~ r1_tarski(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_79]),c_0_106])])).

cnf(c_0_119,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,k1_tarski(X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k2_pre_topc(X1,k1_tarski(X3)))
    | ~ r1_tarski(k1_tarski(X3),u1_struct_0(X1))
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_79])).

cnf(c_0_120,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | r1_tarski(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),k2_pre_topc(esk2_0,k1_tarski(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_79]),c_0_106])])).

cnf(c_0_121,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(k2_pre_topc(X1,X2),X3)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ r1_tarski(X2,u1_struct_0(X1))
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_33])).

cnf(c_0_122,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))) = k2_pre_topc(esk2_0,k1_tarski(esk3_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | ~ m1_subset_1(k1_tarski(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_92]),c_0_75])])).

cnf(c_0_123,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))) = k2_pre_topc(esk2_0,k1_tarski(esk4_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))))
    | ~ r1_tarski(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),u1_struct_0(esk2_0))
    | ~ r1_tarski(k1_tarski(esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_87]),c_0_75])])).

cnf(c_0_124,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_tdlat_3(X1)
    | ~ v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(k2_pre_topc(X1,X2),X3)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ r1_tarski(X2,u1_struct_0(X1))
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_51])).

cnf(c_0_125,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))) = k2_pre_topc(esk2_0,k1_tarski(esk3_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | ~ r1_tarski(k1_tarski(esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_33])).

cnf(c_0_126,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))) = k2_pre_topc(esk2_0,k1_tarski(esk4_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))))
    | ~ r1_tarski(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_79]),c_0_85])])).

cnf(c_0_127,plain,
    ( k2_pre_topc(X1,X2) = k1_xboole_0
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_xboole_0(k2_pre_topc(X1,X2),X3)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_37]),c_0_45]),c_0_49])).

cnf(c_0_128,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))) = k2_pre_topc(esk2_0,k1_tarski(esk3_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_79]),c_0_106])])).

cnf(c_0_129,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))) = k2_pre_topc(esk2_0,k1_tarski(esk4_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))))
    | ~ m1_subset_1(k1_tarski(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_92]),c_0_75])])).

cnf(c_0_130,negated_conjecture,
    ( k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) != k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_131,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | ~ m1_subset_1(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_xboole_0(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),X1)
    | ~ r1_tarski(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),k2_pre_topc(esk2_0,X1))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_86]),c_0_87]),c_0_75])])).

cnf(c_0_132,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))) = k2_pre_topc(esk2_0,k1_tarski(esk4_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))))
    | ~ r1_tarski(k1_tarski(esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_33])).

cnf(c_0_133,negated_conjecture,
    ( k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) != k2_pre_topc(esk2_0,k1_tarski(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_130,c_0_109])).

cnf(c_0_134,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk3_0) = k1_tarski(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_102]),c_0_82])).

cnf(c_0_135,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | ~ m1_subset_1(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_xboole_0(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),k1_tarski(esk4_0))
    | ~ r1_tarski(k1_tarski(esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_131,c_0_120])).

cnf(c_0_136,negated_conjecture,
    ( k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))) = k2_pre_topc(esk2_0,k1_tarski(esk4_0))
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_79]),c_0_106])])).

cnf(c_0_137,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) != k2_pre_topc(esk2_0,k1_tarski(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_138,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | ~ m1_subset_1(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_xboole_0(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),k1_tarski(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_79]),c_0_85])])).

cnf(c_0_139,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,k1_tarski(esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_128]),c_0_137])).

fof(c_0_140,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | ~ v1_xboole_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_141,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | ~ m1_subset_1(k2_pre_topc(esk2_0,k1_tarski(esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_64]),c_0_139])).

cnf(c_0_142,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_140])).

cnf(c_0_143,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | ~ m1_subset_1(k1_tarski(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_37]),c_0_75])])).

cnf(c_0_144,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_145,negated_conjecture,
    ( ~ v1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))) ),
    inference(spm,[status(thm)],[c_0_142,c_0_108])).

cnf(c_0_146,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0
    | k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | ~ r1_tarski(k1_tarski(esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_143,c_0_33])).

cnf(c_0_147,plain,
    ( r2_hidden(X1,k2_pre_topc(X2,k1_tarski(X1)))
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_144,c_0_41])).

cnf(c_0_148,negated_conjecture,
    ( ~ v1_xboole_0(k2_pre_topc(esk2_0,k1_tarski(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_145,c_0_109])).

cnf(c_0_149,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0
    | k2_pre_topc(esk2_0,k1_tarski(esk4_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_79]),c_0_106])])).

cnf(c_0_150,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_151,plain,
    ( ~ v1_xboole_0(k2_pre_topc(X1,k1_tarski(X2)))
    | ~ m1_subset_1(k1_tarski(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_142,c_0_147])).

cnf(c_0_152,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tarski(esk3_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_150])])).

cnf(c_0_153,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_152]),c_0_150]),c_0_75])])).

cnf(c_0_154,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_153,c_0_33])).

cnf(c_0_155,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_79]),c_0_106])]),
    [proof]).

%------------------------------------------------------------------------------
