%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:21 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 376 expanded)
%              Number of clauses        :   58 ( 158 expanded)
%              Number of leaves         :   12 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  500 (3040 expanded)
%              Number of equality atoms :   16 ( 161 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal clause size      :   90 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t60_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v3_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(t62_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(d12_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( v4_pre_topc(X4,X2)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(t61_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v4_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(c_0_12,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_13,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X31,X32] :
      ( ( v3_pre_topc(X32,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))
        | ~ v3_pre_topc(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))))
        | ~ v3_pre_topc(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( v3_pre_topc(X32,X31)
        | ~ v3_pre_topc(X32,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ v3_pre_topc(X32,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).

fof(c_0_17,plain,(
    ! [X25,X26] :
      ( ( ~ v3_pre_topc(X26,X25)
        | r2_hidden(X26,u1_pre_topc(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( ~ r2_hidden(X26,u1_pre_topc(X25))
        | v3_pre_topc(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ r1_tarski(X19,u1_pre_topc(X18))
        | r2_hidden(k5_setfam_1(u1_struct_0(X18),X19),u1_pre_topc(X18))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r2_hidden(X20,u1_pre_topc(X18))
        | ~ r2_hidden(X21,u1_pre_topc(X18))
        | r2_hidden(k9_subset_1(u1_struct_0(X18),X20,X21),u1_pre_topc(X18))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk3_1(X18),k1_zfmisc_1(u1_struct_0(X18)))
        | m1_subset_1(esk2_1(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk4_1(X18),k1_zfmisc_1(u1_struct_0(X18)))
        | m1_subset_1(esk2_1(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk3_1(X18),u1_pre_topc(X18))
        | m1_subset_1(esk2_1(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk4_1(X18),u1_pre_topc(X18))
        | m1_subset_1(esk2_1(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X18),esk3_1(X18),esk4_1(X18)),u1_pre_topc(X18))
        | m1_subset_1(esk2_1(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk3_1(X18),k1_zfmisc_1(u1_struct_0(X18)))
        | r1_tarski(esk2_1(X18),u1_pre_topc(X18))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk4_1(X18),k1_zfmisc_1(u1_struct_0(X18)))
        | r1_tarski(esk2_1(X18),u1_pre_topc(X18))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk3_1(X18),u1_pre_topc(X18))
        | r1_tarski(esk2_1(X18),u1_pre_topc(X18))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk4_1(X18),u1_pre_topc(X18))
        | r1_tarski(esk2_1(X18),u1_pre_topc(X18))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X18),esk3_1(X18),esk4_1(X18)),u1_pre_topc(X18))
        | r1_tarski(esk2_1(X18),u1_pre_topc(X18))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk3_1(X18),k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X18),esk2_1(X18)),u1_pre_topc(X18))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk4_1(X18),k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X18),esk2_1(X18)),u1_pre_topc(X18))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk3_1(X18),u1_pre_topc(X18))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X18),esk2_1(X18)),u1_pre_topc(X18))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk4_1(X18),u1_pre_topc(X18))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X18),esk2_1(X18)),u1_pre_topc(X18))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X18),esk3_1(X18),esk4_1(X18)),u1_pre_topc(X18))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X18),esk2_1(X18)),u1_pre_topc(X18))
        | ~ r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))
        | v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X30] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30)))
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30)))
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) )
                   => ( X3 = X4
                     => ( v5_pre_topc(X3,X1,X2)
                      <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_pre_topc])).

cnf(c_0_33,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31])).

fof(c_0_35,plain,(
    ! [X27,X28] :
      ( ( v1_pre_topc(g1_pre_topc(X27,X28))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))) )
      & ( l1_pre_topc(g1_pre_topc(X27,X28))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_36,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | m1_subset_1(u1_pre_topc(X29),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X29)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_struct_0(esk6_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_struct_0(esk6_0))))
    & esk7_0 = esk8_0
    & ( ~ v5_pre_topc(esk7_0,esk5_0,esk6_0)
      | ~ v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0) )
    & ( v5_pre_topc(esk7_0,esk5_0,esk6_0)
      | v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

fof(c_0_38,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ v5_pre_topc(X15,X13,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ v4_pre_topc(X16,X14)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,X16),X13)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X14)))
        | v5_pre_topc(X15,X13,X14)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( v4_pre_topc(esk1_3(X13,X14,X15),X14)
        | v5_pre_topc(X15,X13,X14)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,esk1_3(X13,X14,X15)),X13)
        | v5_pre_topc(X15,X13,X14)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

fof(c_0_39,plain,(
    ! [X33,X34] :
      ( ( v4_pre_topc(X34,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))
        | ~ v4_pre_topc(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))))
        | ~ v4_pre_topc(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v4_pre_topc(X34,X33)
        | ~ v4_pre_topc(X34,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v4_pre_topc(X34,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_pre_topc])])])])).

cnf(c_0_40,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_30])])).

cnf(c_0_41,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X9,X10,X11,X12] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | m1_subset_1(k8_relset_1(X9,X10,X11,X12),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

cnf(c_0_47,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_50,plain,
    ( v4_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_struct_0(esk6_0)))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_56,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_57,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v2_pre_topc(X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3),X1,esk1_3(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3,X1)),X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3),X1,esk1_3(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3,X1)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_21]),c_0_30])]),c_0_29])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( v4_pre_topc(esk1_3(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0,esk7_0),esk6_0)
    | v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_54])])).

cnf(c_0_62,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2),X3,X4),X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_pre_topc(X4,X2)
    | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_63,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v2_pre_topc(X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,esk1_3(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3,X1)),X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_57])).

cnf(c_0_64,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | m1_subset_1(esk1_3(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3,X1),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( v4_pre_topc(esk1_3(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0,esk7_0),esk6_0)
    | v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_41])).

cnf(c_0_66,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_67,negated_conjecture,
    ( v5_pre_topc(esk7_0,esk5_0,esk6_0)
    | v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_68,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_pre_topc(X4,X2)
    | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( ~ v5_pre_topc(esk7_0,esk5_0,esk6_0)
    | ~ v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_70,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v2_pre_topc(X2)
    | ~ v4_pre_topc(esk1_3(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3,X1),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_56]),c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( v4_pre_topc(esk1_3(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0,esk7_0),esk6_0)
    | v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_42]),c_0_66])])).

cnf(c_0_72,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_75,negated_conjecture,
    ( v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)
    | v5_pre_topc(esk7_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_67,c_0_44])).

cnf(c_0_76,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v2_pre_topc(X2)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_68]),c_0_60]),c_0_50])).

cnf(c_0_77,negated_conjecture,
    ( ~ v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)
    | ~ v5_pre_topc(esk7_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_44])).

cnf(c_0_78,negated_conjecture,
    ( v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_73]),c_0_53]),c_0_54]),c_0_66]),c_0_74])]),c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( v5_pre_topc(esk7_0,esk5_0,esk6_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_75]),c_0_72]),c_0_73]),c_0_53]),c_0_54]),c_0_66]),c_0_74])])).

cnf(c_0_80,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_81,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_41])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_42]),c_0_66])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.42  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.033 s
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.42  fof(t60_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v3_pre_topc(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 0.19/0.42  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.19/0.42  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.19/0.42  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.19/0.42  fof(t62_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.19/0.42  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.19/0.42  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.42  fof(d12_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X4,X2)=>v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_pre_topc)).
% 0.19/0.42  fof(t61_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v4_pre_topc(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_pre_topc)).
% 0.19/0.42  fof(dt_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 0.19/0.42  fof(c_0_12, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.42  fof(c_0_13, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.42  cnf(c_0_14, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  fof(c_0_16, plain, ![X31, X32]:(((v3_pre_topc(X32,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))|(~v3_pre_topc(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))))|(~v3_pre_topc(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(~v2_pre_topc(X31)|~l1_pre_topc(X31))))&((v3_pre_topc(X32,X31)|(~v3_pre_topc(X32,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31))))))|(~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(~v3_pre_topc(X32,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31))))))|(~v2_pre_topc(X31)|~l1_pre_topc(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).
% 0.19/0.42  fof(c_0_17, plain, ![X25, X26]:((~v3_pre_topc(X26,X25)|r2_hidden(X26,u1_pre_topc(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_pre_topc(X25))&(~r2_hidden(X26,u1_pre_topc(X25))|v3_pre_topc(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_pre_topc(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.19/0.42  cnf(c_0_18, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_19, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.42  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_21, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  fof(c_0_22, plain, ![X18, X19, X20, X21]:((((r2_hidden(u1_struct_0(X18),u1_pre_topc(X18))|~v2_pre_topc(X18)|~l1_pre_topc(X18))&(~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|(~r1_tarski(X19,u1_pre_topc(X18))|r2_hidden(k5_setfam_1(u1_struct_0(X18),X19),u1_pre_topc(X18)))|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X18)))|(~r2_hidden(X20,u1_pre_topc(X18))|~r2_hidden(X21,u1_pre_topc(X18))|r2_hidden(k9_subset_1(u1_struct_0(X18),X20,X21),u1_pre_topc(X18))))|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(((m1_subset_1(esk3_1(X18),k1_zfmisc_1(u1_struct_0(X18)))|(m1_subset_1(esk2_1(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18))&((m1_subset_1(esk4_1(X18),k1_zfmisc_1(u1_struct_0(X18)))|(m1_subset_1(esk2_1(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18))&(((r2_hidden(esk3_1(X18),u1_pre_topc(X18))|(m1_subset_1(esk2_1(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18))&(r2_hidden(esk4_1(X18),u1_pre_topc(X18))|(m1_subset_1(esk2_1(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18)))&(~r2_hidden(k9_subset_1(u1_struct_0(X18),esk3_1(X18),esk4_1(X18)),u1_pre_topc(X18))|(m1_subset_1(esk2_1(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18)))))&(((m1_subset_1(esk3_1(X18),k1_zfmisc_1(u1_struct_0(X18)))|(r1_tarski(esk2_1(X18),u1_pre_topc(X18))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18))&((m1_subset_1(esk4_1(X18),k1_zfmisc_1(u1_struct_0(X18)))|(r1_tarski(esk2_1(X18),u1_pre_topc(X18))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18))&(((r2_hidden(esk3_1(X18),u1_pre_topc(X18))|(r1_tarski(esk2_1(X18),u1_pre_topc(X18))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18))&(r2_hidden(esk4_1(X18),u1_pre_topc(X18))|(r1_tarski(esk2_1(X18),u1_pre_topc(X18))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18)))&(~r2_hidden(k9_subset_1(u1_struct_0(X18),esk3_1(X18),esk4_1(X18)),u1_pre_topc(X18))|(r1_tarski(esk2_1(X18),u1_pre_topc(X18))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18)))))&((m1_subset_1(esk3_1(X18),k1_zfmisc_1(u1_struct_0(X18)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X18),esk2_1(X18)),u1_pre_topc(X18))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18))&((m1_subset_1(esk4_1(X18),k1_zfmisc_1(u1_struct_0(X18)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X18),esk2_1(X18)),u1_pre_topc(X18))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18))&(((r2_hidden(esk3_1(X18),u1_pre_topc(X18))|(~r2_hidden(k5_setfam_1(u1_struct_0(X18),esk2_1(X18)),u1_pre_topc(X18))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18))&(r2_hidden(esk4_1(X18),u1_pre_topc(X18))|(~r2_hidden(k5_setfam_1(u1_struct_0(X18),esk2_1(X18)),u1_pre_topc(X18))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18)))&(~r2_hidden(k9_subset_1(u1_struct_0(X18),esk3_1(X18),esk4_1(X18)),u1_pre_topc(X18))|(~r2_hidden(k5_setfam_1(u1_struct_0(X18),esk2_1(X18)),u1_pre_topc(X18))|~r2_hidden(u1_struct_0(X18),u1_pre_topc(X18)))|v2_pre_topc(X18)|~l1_pre_topc(X18)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.19/0.42  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_24, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 0.19/0.42  fof(c_0_25, plain, ![X30]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30)))|(~v2_pre_topc(X30)|~l1_pre_topc(X30)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30)))|(~v2_pre_topc(X30)|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.19/0.42  cnf(c_0_26, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_19, c_0_15])).
% 0.19/0.42  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.42  cnf(c_0_29, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.42  cnf(c_0_31, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  fof(c_0_32, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)))))))), inference(assume_negation,[status(cth)],[t62_pre_topc])).
% 0.19/0.42  cnf(c_0_33, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=X2|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.42  cnf(c_0_34, plain, (m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])]), c_0_31])).
% 0.19/0.42  fof(c_0_35, plain, ![X27, X28]:((v1_pre_topc(g1_pre_topc(X27,X28))|~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))))&(l1_pre_topc(g1_pre_topc(X27,X28))|~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.19/0.42  fof(c_0_36, plain, ![X29]:(~l1_pre_topc(X29)|m1_subset_1(u1_pre_topc(X29),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X29))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.42  fof(c_0_37, negated_conjecture, ((v2_pre_topc(esk5_0)&l1_pre_topc(esk5_0))&((v2_pre_topc(esk6_0)&l1_pre_topc(esk6_0))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0)))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_struct_0(esk6_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_struct_0(esk6_0)))))&(esk7_0=esk8_0&((~v5_pre_topc(esk7_0,esk5_0,esk6_0)|~v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0))&(v5_pre_topc(esk7_0,esk5_0,esk6_0)|v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.19/0.42  fof(c_0_38, plain, ![X13, X14, X15, X16]:((~v5_pre_topc(X15,X13,X14)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(~v4_pre_topc(X16,X14)|v4_pre_topc(k8_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,X16),X13)))|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|~l1_pre_topc(X14)|~l1_pre_topc(X13))&((m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X14)))|v5_pre_topc(X15,X13,X14)|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|~l1_pre_topc(X14)|~l1_pre_topc(X13))&((v4_pre_topc(esk1_3(X13,X14,X15),X14)|v5_pre_topc(X15,X13,X14)|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|~l1_pre_topc(X14)|~l1_pre_topc(X13))&(~v4_pre_topc(k8_relset_1(u1_struct_0(X13),u1_struct_0(X14),X15,esk1_3(X13,X14,X15)),X13)|v5_pre_topc(X15,X13,X14)|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14)))))|~l1_pre_topc(X14)|~l1_pre_topc(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).
% 0.19/0.42  fof(c_0_39, plain, ![X33, X34]:(((v4_pre_topc(X34,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))|(~v4_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))))|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))))|(~v4_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))))|(~v2_pre_topc(X33)|~l1_pre_topc(X33))))&((v4_pre_topc(X34,X33)|(~v4_pre_topc(X34,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33))))))|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(~v4_pre_topc(X34,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33))))))|(~v2_pre_topc(X33)|~l1_pre_topc(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_pre_topc])])])])).
% 0.19/0.42  cnf(c_0_40, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(X1)|~v3_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_30])])).
% 0.19/0.42  cnf(c_0_41, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_42, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.42  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_struct_0(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (esk7_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  fof(c_0_46, plain, ![X9, X10, X11, X12]:(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|m1_subset_1(k8_relset_1(X9,X10,X11,X12),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).
% 0.19/0.42  cnf(c_0_47, plain, (v5_pre_topc(X3,X1,X2)|~v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.42  cnf(c_0_48, plain, (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.42  cnf(c_0_49, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(X1)|~v3_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.19/0.42  cnf(c_0_50, plain, (v4_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.42  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_struct_0(esk6_0))))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_struct_0(esk6_0))), inference(rw,[status(thm)],[c_0_45, c_0_44])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_55, plain, (v4_pre_topc(X1,X2)|~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.42  cnf(c_0_56, plain, (v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v4_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.42  cnf(c_0_57, plain, (m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.42  cnf(c_0_58, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v2_pre_topc(X2)|~v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3),X1,esk1_3(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3,X1)),X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_1(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3),X1,esk1_3(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3,X1)),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.42  cnf(c_0_59, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_21]), c_0_30])]), c_0_29])).
% 0.19/0.42  cnf(c_0_60, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (v4_pre_topc(esk1_3(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0,esk7_0),esk6_0)|v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53]), c_0_54])])).
% 0.19/0.42  cnf(c_0_62, plain, (v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2),X3,X4),X1)|~v2_pre_topc(X1)|~v4_pre_topc(X4,X2)|~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))|~v1_funct_1(X3)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.19/0.42  cnf(c_0_63, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v2_pre_topc(X2)|~v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,esk1_3(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3,X1)),X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_57])).
% 0.19/0.42  cnf(c_0_64, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|m1_subset_1(esk1_3(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3,X1),k1_zfmisc_1(u1_struct_0(X3)))|~v2_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(spm,[status(thm)],[c_0_60, c_0_59])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (v4_pre_topc(esk1_3(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0,esk7_0),esk6_0)|v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)|~m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_61, c_0_41])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (v5_pre_topc(esk7_0,esk5_0,esk6_0)|v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_68, plain, (v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)|~v2_pre_topc(X1)|~v4_pre_topc(X4,X2)|~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_62, c_0_59])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (~v5_pre_topc(esk7_0,esk5_0,esk6_0)|~v5_pre_topc(esk8_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_70, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v2_pre_topc(X2)|~v4_pre_topc(esk1_3(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3,X1),X3)|~v5_pre_topc(X1,X2,X3)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_56]), c_0_64])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, (v4_pre_topc(esk1_3(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0,esk7_0),esk6_0)|v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_42]), c_0_66])])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_73, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_75, negated_conjecture, (v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)|v5_pre_topc(esk7_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_67, c_0_44])).
% 0.19/0.42  cnf(c_0_76, plain, (v5_pre_topc(X1,X2,X3)|~v2_pre_topc(X2)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_68]), c_0_60]), c_0_50])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, (~v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)|~v5_pre_topc(esk7_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_69, c_0_44])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_73]), c_0_53]), c_0_54]), c_0_66]), c_0_74])]), c_0_75])).
% 0.19/0.42  cnf(c_0_79, negated_conjecture, (v5_pre_topc(esk7_0,esk5_0,esk6_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_75]), c_0_72]), c_0_73]), c_0_53]), c_0_54]), c_0_66]), c_0_74])])).
% 0.19/0.42  cnf(c_0_80, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.19/0.42  cnf(c_0_81, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_80, c_0_41])).
% 0.19/0.42  cnf(c_0_82, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_42]), c_0_66])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 83
% 0.19/0.42  # Proof object clause steps            : 58
% 0.19/0.42  # Proof object formula steps           : 25
% 0.19/0.42  # Proof object conjectures             : 26
% 0.19/0.42  # Proof object clause conjectures      : 23
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 29
% 0.19/0.42  # Proof object initial formulas used   : 12
% 0.19/0.42  # Proof object generating inferences   : 24
% 0.19/0.42  # Proof object simplifying inferences  : 43
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 12
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 56
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 56
% 0.19/0.42  # Processed clauses                    : 185
% 0.19/0.42  # ...of these trivial                  : 2
% 0.19/0.42  # ...subsumed                          : 37
% 0.19/0.42  # ...remaining for further processing  : 146
% 0.19/0.42  # Other redundant clauses eliminated   : 2
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 16
% 0.19/0.42  # Backward-rewritten                   : 1
% 0.19/0.42  # Generated clauses                    : 592
% 0.19/0.42  # ...of the previous two non-trivial   : 543
% 0.19/0.42  # Contextual simplify-reflections      : 36
% 0.19/0.42  # Paramodulations                      : 590
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 2
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 127
% 0.19/0.42  #    Positive orientable unit clauses  : 12
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 2
% 0.19/0.42  #    Non-unit-clauses                  : 113
% 0.19/0.42  # Current number of unprocessed clauses: 413
% 0.19/0.42  # ...number of literals in the above   : 3906
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 17
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 7104
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 604
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 89
% 0.19/0.42  # Unit Clause-clause subsumption calls : 65
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 26
% 0.19/0.42  # BW rewrite match successes           : 1
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 40674
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.070 s
% 0.19/0.42  # System time              : 0.006 s
% 0.19/0.42  # Total time               : 0.077 s
% 0.19/0.42  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
