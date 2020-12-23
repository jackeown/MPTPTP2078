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
% DateTime   : Thu Dec  3 11:12:42 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  151 (8693 expanded)
%              Number of clauses        :  104 (3462 expanded)
%              Number of leaves         :   23 (2277 expanded)
%              Depth                    :   20
%              Number of atoms          :  482 (33880 expanded)
%              Number of equality atoms :   81 (4684 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t49_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(projectivity_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d7_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v5_tops_1(X2,X1)
          <=> X2 = k2_pre_topc(X1,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(d6_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
          <=> ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
              & r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t110_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
           => k1_tops_1(X1,k2_tops_1(X1,X2)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_tops_1)).

fof(t58_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,k1_tops_1(X1,X2)) = k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(projectivity_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(t73_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_xboole_0(k1_tops_1(X1,X2),k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(d2_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(t69_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(c_0_23,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_24,plain,(
    ! [X21,X22,X23] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ r1_tarski(X22,X23)
      | r1_tarski(k2_pre_topc(X21,X22),k2_pre_topc(X21,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

fof(c_0_25,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | k2_pre_topc(X17,k2_pre_topc(X17,X18)) = k2_pre_topc(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | m1_subset_1(k2_pre_topc(X15,X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_27,plain,(
    ! [X30,X31] :
      ( ( ~ v5_tops_1(X31,X30)
        | X31 = k2_pre_topc(X30,k1_tops_1(X30,X31))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( X31 != k2_pre_topc(X30,k1_tops_1(X30,X31))
        | v5_tops_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X28,X29] :
      ( ( r1_tarski(k1_tops_1(X28,k2_pre_topc(X28,X29)),X29)
        | ~ v4_tops_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( r1_tarski(X29,k2_pre_topc(X28,k1_tops_1(X28,X29)))
        | ~ v4_tops_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( ~ r1_tarski(k1_tops_1(X28,k2_pre_topc(X28,X29)),X29)
        | ~ r1_tarski(X29,k2_pre_topc(X28,k1_tops_1(X28,X29)))
        | v4_tops_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).

fof(c_0_33,plain,(
    ! [X42,X43,X44] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
      | ~ v4_pre_topc(X43,X42)
      | ~ r1_tarski(X44,X43)
      | r1_tarski(k2_pre_topc(X42,X44),X43) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).

fof(c_0_34,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | m1_subset_1(k1_tops_1(X32,X33),k1_zfmisc_1(u1_struct_0(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_tops_1(X2,X1)
             => k1_tops_1(X1,k2_tops_1(X1,X2)) = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t110_tops_1])).

cnf(c_0_36,plain,
    ( v5_tops_1(X1,X2)
    | X1 != k2_pre_topc(X2,k1_tops_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X50,X51] :
      ( ~ l1_pre_topc(X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
      | k2_pre_topc(X50,k1_tops_1(X50,X51)) = k2_pre_topc(X50,k1_tops_1(X50,k2_pre_topc(X50,k1_tops_1(X50,X51)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_tops_1])])])).

cnf(c_0_38,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

fof(c_0_40,plain,(
    ! [X45,X46] :
      ( ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
      | r1_tarski(k1_tops_1(X45,X46),X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_41,plain,(
    ! [X47,X48,X49] :
      ( ~ l1_pre_topc(X47)
      | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47)))
      | ~ r1_tarski(X48,X49)
      | r1_tarski(k1_tops_1(X47,X48),k1_tops_1(X47,X49)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

fof(c_0_42,plain,(
    ! [X38,X39] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | k1_tops_1(X38,k1_tops_1(X38,X39)) = k1_tops_1(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))
    | ~ v4_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_pre_topc(X1,X3),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( X1 = k2_pre_topc(X2,k1_tops_1(X2,X1))
    | ~ v5_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_47,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v4_tops_1(esk2_0,esk1_0)
    & k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).

cnf(c_0_48,plain,
    ( v5_tops_1(k2_pre_topc(X1,X2),X1)
    | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2))) != k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_49,plain,
    ( k2_pre_topc(X1,k1_tops_1(X1,X2)) = k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( k2_pre_topc(X1,k1_tops_1(X1,X2)) = X2
    | ~ v4_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_43])).

cnf(c_0_55,plain,
    ( r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X2)),X3)
    | ~ v4_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,plain,
    ( k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,X2)
    | ~ v5_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( v5_tops_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_45])).

cnf(c_0_60,plain,
    ( k2_pre_topc(X1,k1_tops_1(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ v4_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_43]),c_0_51]),c_0_45])).

cnf(c_0_61,plain,
    ( k1_tops_1(X1,X2) = k1_tops_1(X1,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_52])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_45])).

fof(c_0_63,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | r1_tarski(X20,k2_pre_topc(X19,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_64,plain,
    ( k2_pre_topc(X1,k1_tops_1(X1,X2)) = X2
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))) = k2_pre_topc(esk1_0,esk2_0)
    | ~ v5_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_66,plain,
    ( v5_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ v4_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( v4_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_68,plain,
    ( k1_tops_1(X1,X2) = k1_tops_1(X1,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ v4_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_70,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,X2)
    | ~ v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v4_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_31])).

fof(c_0_72,plain,(
    ! [X36,X37] :
      ( ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | v4_pre_topc(k2_pre_topc(X36,X37),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_73,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_58]),c_0_57])])).

cnf(c_0_74,plain,
    ( k1_tops_1(X1,k2_pre_topc(X1,X2)) = k1_tops_1(X1,X2)
    | ~ v4_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_31])).

cnf(c_0_75,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))) = k2_pre_topc(esk1_0,esk2_0)
    | ~ v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_57]),c_0_58])])).

cnf(c_0_76,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_78,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | k1_tops_1(X24,X25) = k3_subset_1(u1_struct_0(X24),k2_pre_topc(X24,k3_subset_1(u1_struct_0(X24),X25))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

fof(c_0_79,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | k3_subset_1(X13,k3_subset_1(X13,X14)) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_80,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | m1_subset_1(k3_subset_1(X11,X12),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_73]),c_0_58])])).

cnf(c_0_82,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_57]),c_0_67]),c_0_58])])).

cnf(c_0_83,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))) = k2_pre_topc(esk1_0,esk2_0)
    | ~ v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_58]),c_0_57])])).

cnf(c_0_84,plain,
    ( v4_tops_1(X2,X1)
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_86,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_87,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_88,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | ~ v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_83]),c_0_58])])).

cnf(c_0_91,plain,
    ( v4_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_30]),c_0_51]),c_0_31])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_93,plain,
    ( k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_82]),c_0_58])])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_45]),c_0_58]),c_0_57])])).

cnf(c_0_96,plain,
    ( k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2)) = k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_86])).

cnf(c_0_97,negated_conjecture,
    ( k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | ~ v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_45]),c_0_58])])).

cnf(c_0_98,negated_conjecture,
    ( v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_73]),c_0_58]),c_0_57]),c_0_92])])).

cnf(c_0_99,plain,
    ( k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_93]),c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_82])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])])).

cnf(c_0_102,plain,
    ( k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2)) = k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_31]),c_0_88])).

cnf(c_0_103,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_93]),c_0_88])).

cnf(c_0_104,negated_conjecture,
    ( k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98])])).

cnf(c_0_105,plain,
    ( m1_subset_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_49])).

cnf(c_0_106,negated_conjecture,
    ( k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))) = k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_58]),c_0_101])])).

cnf(c_0_107,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))) = k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_82]),c_0_58]),c_0_95])])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_100]),c_0_58]),c_0_101])])).

fof(c_0_109,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X6,X8)
      | ~ r1_xboole_0(X7,X8)
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

fof(c_0_110,plain,(
    ! [X56,X57] :
      ( ~ l1_pre_topc(X56)
      | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
      | r1_xboole_0(k1_tops_1(X56,X57),k2_tops_1(X56,X57)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_tops_1])])])).

cnf(c_0_111,plain,
    ( k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_tops_1(X1,X2))) = k1_tops_1(X1,k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_86])).

cnf(c_0_112,plain,
    ( k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_87]),c_0_31]),c_0_88])).

cnf(c_0_113,negated_conjecture,
    ( k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_31]),c_0_58]),c_0_57])])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107]),c_0_58]),c_0_107]),c_0_108])])).

cnf(c_0_115,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_82]),c_0_58])])).

cnf(c_0_116,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_117,plain,
    ( r1_xboole_0(k1_tops_1(X1,X2),k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_118,plain,
    ( v4_pre_topc(k2_pre_topc(X1,k1_tops_1(X1,X2)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_49])).

cnf(c_0_119,plain,
    ( k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))) = k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_111])).

cnf(c_0_120,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_106]),c_0_113]),c_0_58]),c_0_95])])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_93]),c_0_100]),c_0_108]),c_0_58]),c_0_101])])).

cnf(c_0_122,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_95])])).

cnf(c_0_123,plain,
    ( v4_tops_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_49]),c_0_92])]),c_0_45])).

cnf(c_0_124,plain,
    ( X1 = k1_xboole_0
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_tops_1(X2,X3))
    | ~ r1_tarski(X1,k1_tops_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

fof(c_0_125,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | m1_subset_1(k2_tops_1(X34,X35),k1_zfmisc_1(u1_struct_0(X34))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_126,plain,
    ( v4_pre_topc(k2_pre_topc(X1,k1_tops_1(X1,X2)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_45])).

cnf(c_0_127,negated_conjecture,
    ( k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))) = k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_113]),c_0_82]),c_0_100]),c_0_106]),c_0_107]),c_0_58]),c_0_113]),c_0_95]),c_0_106]),c_0_107]),c_0_121]),c_0_108])])).

cnf(c_0_128,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))) = k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_122]),c_0_58]),c_0_101])])).

cnf(c_0_129,negated_conjecture,
    ( v4_tops_1(k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_106]),c_0_107]),c_0_58]),c_0_108])])).

cnf(c_0_130,plain,
    ( k1_tops_1(X1,k2_tops_1(X2,X3)) = k1_xboole_0
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(k1_tops_1(X1,k2_tops_1(X2,X3)),k1_tops_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_51])).

cnf(c_0_131,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_125])).

cnf(c_0_132,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_83]),c_0_77]),c_0_58])])).

fof(c_0_133,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | k2_tops_1(X26,X27) = k9_subset_1(u1_struct_0(X26),k2_pre_topc(X26,X27),k2_pre_topc(X26,k3_subset_1(u1_struct_0(X26),X27))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_1])])])).

cnf(c_0_134,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_102]),c_0_58]),c_0_57])])).

cnf(c_0_135,negated_conjecture,
    ( k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_102]),c_0_58]),c_0_57])])).

cnf(c_0_136,negated_conjecture,
    ( v4_tops_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_102]),c_0_58]),c_0_57])])).

cnf(c_0_137,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_102]),c_0_58]),c_0_57])])).

cnf(c_0_138,plain,
    ( k1_tops_1(X1,k2_tops_1(X1,X2)) = k1_xboole_0
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_tops_1(X1,X2),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_52]),c_0_131])).

fof(c_0_139,plain,(
    ! [X54,X55] :
      ( ~ l1_pre_topc(X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
      | ~ v4_pre_topc(X55,X54)
      | r1_tarski(k2_tops_1(X54,X55),X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_tops_1])])])).

cnf(c_0_140,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_98])])).

cnf(c_0_141,plain,
    ( k2_tops_1(X1,X2) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_133])).

cnf(c_0_142,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_134]),c_0_107]),c_0_135]),c_0_136]),c_0_58]),c_0_137])])).

cnf(c_0_143,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))) = k1_xboole_0
    | ~ r1_tarski(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_95]),c_0_58])])).

cnf(c_0_144,plain,
    ( r1_tarski(k2_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_139])).

cnf(c_0_145,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_95])])).

cnf(c_0_146,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_113]),c_0_58])]),c_0_107]),c_0_142]),c_0_95])])).

cnf(c_0_147,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_145]),c_0_58]),c_0_95])])).

cnf(c_0_148,negated_conjecture,
    ( k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_146]),c_0_58]),c_0_57])])).

cnf(c_0_149,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_150,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_147,c_0_148]),c_0_149]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.81/2.00  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.81/2.00  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.81/2.00  #
% 1.81/2.00  # Preprocessing time       : 0.029 s
% 1.81/2.00  # Presaturation interreduction done
% 1.81/2.00  
% 1.81/2.00  # Proof found!
% 1.81/2.00  # SZS status Theorem
% 1.81/2.00  # SZS output start CNFRefutation
% 1.81/2.00  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.81/2.00  fof(t49_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 1.81/2.00  fof(projectivity_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 1.81/2.00  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 1.81/2.00  fof(d7_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v5_tops_1(X2,X1)<=>X2=k2_pre_topc(X1,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 1.81/2.00  fof(d6_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)<=>(r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)&r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 1.81/2.00  fof(t31_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)&r1_tarski(X3,X2))=>r1_tarski(k2_pre_topc(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 1.81/2.00  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 1.81/2.00  fof(t110_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)=>k1_tops_1(X1,k2_tops_1(X1,X2))=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_tops_1)).
% 1.81/2.00  fof(t58_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,k1_tops_1(X1,X2))=k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tops_1)).
% 1.81/2.00  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 1.81/2.00  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 1.81/2.00  fof(projectivity_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 1.81/2.00  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 1.81/2.00  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 1.81/2.00  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 1.81/2.00  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.81/2.00  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.81/2.00  fof(t67_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.81/2.00  fof(t73_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_xboole_0(k1_tops_1(X1,X2),k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tops_1)).
% 1.81/2.00  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 1.81/2.00  fof(d2_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 1.81/2.00  fof(t69_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 1.81/2.00  fof(c_0_23, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.81/2.00  fof(c_0_24, plain, ![X21, X22, X23]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~r1_tarski(X22,X23)|r1_tarski(k2_pre_topc(X21,X22),k2_pre_topc(X21,X23)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).
% 1.81/2.00  fof(c_0_25, plain, ![X17, X18]:(~l1_pre_topc(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|k2_pre_topc(X17,k2_pre_topc(X17,X18))=k2_pre_topc(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).
% 1.81/2.00  fof(c_0_26, plain, ![X15, X16]:(~l1_pre_topc(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|m1_subset_1(k2_pre_topc(X15,X16),k1_zfmisc_1(u1_struct_0(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 1.81/2.00  fof(c_0_27, plain, ![X30, X31]:((~v5_tops_1(X31,X30)|X31=k2_pre_topc(X30,k1_tops_1(X30,X31))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&(X31!=k2_pre_topc(X30,k1_tops_1(X30,X31))|v5_tops_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).
% 1.81/2.00  cnf(c_0_28, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.81/2.00  cnf(c_0_29, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.81/2.00  cnf(c_0_30, plain, (k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.81/2.00  cnf(c_0_31, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.81/2.00  fof(c_0_32, plain, ![X28, X29]:(((r1_tarski(k1_tops_1(X28,k2_pre_topc(X28,X29)),X29)|~v4_tops_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(r1_tarski(X29,k2_pre_topc(X28,k1_tops_1(X28,X29)))|~v4_tops_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28)))&(~r1_tarski(k1_tops_1(X28,k2_pre_topc(X28,X29)),X29)|~r1_tarski(X29,k2_pre_topc(X28,k1_tops_1(X28,X29)))|v4_tops_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).
% 1.81/2.00  fof(c_0_33, plain, ![X42, X43, X44]:(~l1_pre_topc(X42)|(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|(~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|(~v4_pre_topc(X43,X42)|~r1_tarski(X44,X43)|r1_tarski(k2_pre_topc(X42,X44),X43))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).
% 1.81/2.00  fof(c_0_34, plain, ![X32, X33]:(~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|m1_subset_1(k1_tops_1(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 1.81/2.00  fof(c_0_35, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)=>k1_tops_1(X1,k2_tops_1(X1,X2))=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t110_tops_1])).
% 1.81/2.00  cnf(c_0_36, plain, (v5_tops_1(X1,X2)|X1!=k2_pre_topc(X2,k1_tops_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.81/2.00  fof(c_0_37, plain, ![X50, X51]:(~l1_pre_topc(X50)|(~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))|k2_pre_topc(X50,k1_tops_1(X50,X51))=k2_pre_topc(X50,k1_tops_1(X50,k2_pre_topc(X50,k1_tops_1(X50,X51)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_tops_1])])])).
% 1.81/2.00  cnf(c_0_38, plain, (k2_pre_topc(X1,X2)=k2_pre_topc(X1,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.81/2.00  cnf(c_0_39, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k2_pre_topc(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 1.81/2.00  fof(c_0_40, plain, ![X45, X46]:(~l1_pre_topc(X45)|(~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|r1_tarski(k1_tops_1(X45,X46),X46))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 1.81/2.00  fof(c_0_41, plain, ![X47, X48, X49]:(~l1_pre_topc(X47)|(~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|(~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47)))|(~r1_tarski(X48,X49)|r1_tarski(k1_tops_1(X47,X48),k1_tops_1(X47,X49)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 1.81/2.00  fof(c_0_42, plain, ![X38, X39]:(~l1_pre_topc(X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|k1_tops_1(X38,k1_tops_1(X38,X39))=k1_tops_1(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).
% 1.81/2.00  cnf(c_0_43, plain, (r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))|~v4_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.81/2.00  cnf(c_0_44, plain, (r1_tarski(k2_pre_topc(X1,X3),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.81/2.00  cnf(c_0_45, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.81/2.00  cnf(c_0_46, plain, (X1=k2_pre_topc(X2,k1_tops_1(X2,X1))|~v5_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.81/2.00  fof(c_0_47, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v4_tops_1(esk2_0,esk1_0)&k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).
% 1.81/2.00  cnf(c_0_48, plain, (v5_tops_1(k2_pre_topc(X1,X2),X1)|k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2)))!=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_36, c_0_31])).
% 1.81/2.00  cnf(c_0_49, plain, (k2_pre_topc(X1,k1_tops_1(X1,X2))=k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.81/2.00  cnf(c_0_50, plain, (k2_pre_topc(X1,X2)=k2_pre_topc(X1,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k2_pre_topc(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.81/2.00  cnf(c_0_51, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.81/2.00  cnf(c_0_52, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.81/2.00  cnf(c_0_53, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.81/2.00  cnf(c_0_54, plain, (k2_pre_topc(X1,k1_tops_1(X1,X2))=X2|~v4_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_28, c_0_43])).
% 1.81/2.00  cnf(c_0_55, plain, (r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X2)),X3)|~v4_pre_topc(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 1.81/2.00  cnf(c_0_56, plain, (k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2)))=k2_pre_topc(X1,X2)|~v5_tops_1(k2_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_46, c_0_31])).
% 1.81/2.00  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.81/2.00  cnf(c_0_58, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.81/2.00  cnf(c_0_59, plain, (v5_tops_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_45])).
% 1.81/2.00  cnf(c_0_60, plain, (k2_pre_topc(X1,k1_tops_1(X1,X2))=k2_pre_topc(X1,X2)|~v4_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_43]), c_0_51]), c_0_45])).
% 1.81/2.00  cnf(c_0_61, plain, (k1_tops_1(X1,X2)=k1_tops_1(X1,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_28, c_0_52])).
% 1.81/2.00  cnf(c_0_62, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_45])).
% 1.81/2.00  fof(c_0_63, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|r1_tarski(X20,k2_pre_topc(X19,X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 1.81/2.00  cnf(c_0_64, plain, (k2_pre_topc(X1,k1_tops_1(X1,X2))=X2|~v4_pre_topc(X2,X1)|~v4_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_51])).
% 1.81/2.00  cnf(c_0_65, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)))=k2_pre_topc(esk1_0,esk2_0)|~v5_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 1.81/2.00  cnf(c_0_66, plain, (v5_tops_1(k2_pre_topc(X1,X2),X1)|~v4_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.81/2.00  cnf(c_0_67, negated_conjecture, (v4_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.81/2.00  cnf(c_0_68, plain, (k1_tops_1(X1,X2)=k1_tops_1(X1,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 1.81/2.00  cnf(c_0_69, plain, (r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~v4_tops_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.81/2.00  cnf(c_0_70, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.81/2.00  cnf(c_0_71, plain, (k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2)))=k2_pre_topc(X1,X2)|~v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v4_tops_1(k2_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_64, c_0_31])).
% 1.81/2.00  fof(c_0_72, plain, ![X36, X37]:(~v2_pre_topc(X36)|~l1_pre_topc(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|v4_pre_topc(k2_pre_topc(X36,X37),X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 1.81/2.00  cnf(c_0_73, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_58]), c_0_57])])).
% 1.81/2.00  cnf(c_0_74, plain, (k1_tops_1(X1,k2_pre_topc(X1,X2))=k1_tops_1(X1,X2)|~v4_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_31])).
% 1.81/2.00  cnf(c_0_75, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)))=k2_pre_topc(esk1_0,esk2_0)|~v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0)|~v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_57]), c_0_58])])).
% 1.81/2.00  cnf(c_0_76, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.81/2.00  cnf(c_0_77, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.81/2.00  fof(c_0_78, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|k1_tops_1(X24,X25)=k3_subset_1(u1_struct_0(X24),k2_pre_topc(X24,k3_subset_1(u1_struct_0(X24),X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 1.81/2.00  fof(c_0_79, plain, ![X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|k3_subset_1(X13,k3_subset_1(X13,X14))=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 1.81/2.00  fof(c_0_80, plain, ![X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|m1_subset_1(k3_subset_1(X11,X12),k1_zfmisc_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 1.81/2.00  cnf(c_0_81, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_73]), c_0_58])])).
% 1.81/2.00  cnf(c_0_82, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_57]), c_0_67]), c_0_58])])).
% 1.81/2.00  cnf(c_0_83, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)))=k2_pre_topc(esk1_0,esk2_0)|~v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_58]), c_0_57])])).
% 1.81/2.00  cnf(c_0_84, plain, (v4_tops_1(X2,X1)|~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.81/2.00  cnf(c_0_85, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.81/2.00  cnf(c_0_86, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 1.81/2.00  cnf(c_0_87, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 1.81/2.00  cnf(c_0_88, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.81/2.00  cnf(c_0_89, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 1.81/2.00  cnf(c_0_90, negated_conjecture, (k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|~v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)|~m1_subset_1(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_83]), c_0_58])])).
% 1.81/2.00  cnf(c_0_91, plain, (v4_tops_1(k2_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_30]), c_0_51]), c_0_31])).
% 1.81/2.00  cnf(c_0_92, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_85])).
% 1.81/2.00  cnf(c_0_93, plain, (k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])).
% 1.81/2.00  cnf(c_0_94, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_82]), c_0_58])])).
% 1.81/2.00  cnf(c_0_95, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_45]), c_0_58]), c_0_57])])).
% 1.81/2.00  cnf(c_0_96, plain, (k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2))=k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_87, c_0_86])).
% 1.81/2.00  cnf(c_0_97, negated_conjecture, (k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|~v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_45]), c_0_58])])).
% 1.81/2.00  cnf(c_0_98, negated_conjecture, (v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_73]), c_0_58]), c_0_57]), c_0_92])])).
% 1.81/2.00  cnf(c_0_99, plain, (k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2)))=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_93]), c_0_88])).
% 1.81/2.00  cnf(c_0_100, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_73, c_0_82])).
% 1.81/2.00  cnf(c_0_101, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])])).
% 1.81/2.00  cnf(c_0_102, plain, (k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2))=k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_31]), c_0_88])).
% 1.81/2.00  cnf(c_0_103, plain, (m1_subset_1(k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_93]), c_0_88])).
% 1.81/2.00  cnf(c_0_104, negated_conjecture, (k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98])])).
% 1.81/2.00  cnf(c_0_105, plain, (m1_subset_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_31, c_0_49])).
% 1.81/2.00  cnf(c_0_106, negated_conjecture, (k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)))=k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_58]), c_0_101])])).
% 1.81/2.00  cnf(c_0_107, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)))=k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_82]), c_0_58]), c_0_95])])).
% 1.81/2.00  cnf(c_0_108, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_100]), c_0_58]), c_0_101])])).
% 1.81/2.00  fof(c_0_109, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X6,X8)|~r1_xboole_0(X7,X8)|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).
% 1.81/2.00  fof(c_0_110, plain, ![X56, X57]:(~l1_pre_topc(X56)|(~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))|r1_xboole_0(k1_tops_1(X56,X57),k2_tops_1(X56,X57)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_tops_1])])])).
% 1.81/2.00  cnf(c_0_111, plain, (k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_tops_1(X1,X2)))=k1_tops_1(X1,k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_86, c_0_86])).
% 1.81/2.00  cnf(c_0_112, plain, (k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_87]), c_0_31]), c_0_88])).
% 1.81/2.00  cnf(c_0_113, negated_conjecture, (k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_31]), c_0_58]), c_0_57])])).
% 1.81/2.00  cnf(c_0_114, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_107]), c_0_58]), c_0_107]), c_0_108])])).
% 1.81/2.00  cnf(c_0_115, negated_conjecture, (k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_82]), c_0_58])])).
% 1.81/2.00  cnf(c_0_116, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_109])).
% 1.81/2.00  cnf(c_0_117, plain, (r1_xboole_0(k1_tops_1(X1,X2),k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_110])).
% 1.81/2.00  cnf(c_0_118, plain, (v4_pre_topc(k2_pre_topc(X1,k1_tops_1(X1,X2)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_76, c_0_49])).
% 1.81/2.00  cnf(c_0_119, plain, (k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))))=k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2)))|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_86, c_0_111])).
% 1.81/2.00  cnf(c_0_120, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_106]), c_0_113]), c_0_58]), c_0_95])])).
% 1.81/2.00  cnf(c_0_121, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_93]), c_0_100]), c_0_108]), c_0_58]), c_0_101])])).
% 1.81/2.00  cnf(c_0_122, negated_conjecture, (k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_95])])).
% 1.81/2.00  cnf(c_0_123, plain, (v4_tops_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_49]), c_0_92])]), c_0_45])).
% 1.81/2.00  cnf(c_0_124, plain, (X1=k1_xboole_0|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_tops_1(X2,X3))|~r1_tarski(X1,k1_tops_1(X2,X3))), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 1.81/2.00  fof(c_0_125, plain, ![X34, X35]:(~l1_pre_topc(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|m1_subset_1(k2_tops_1(X34,X35),k1_zfmisc_1(u1_struct_0(X34)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 1.81/2.00  cnf(c_0_126, plain, (v4_pre_topc(k2_pre_topc(X1,k1_tops_1(X1,X2)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_118, c_0_45])).
% 1.81/2.00  cnf(c_0_127, negated_conjecture, (k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)))=k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_113]), c_0_82]), c_0_100]), c_0_106]), c_0_107]), c_0_58]), c_0_113]), c_0_95]), c_0_106]), c_0_107]), c_0_121]), c_0_108])])).
% 1.81/2.00  cnf(c_0_128, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)))=k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_122]), c_0_58]), c_0_101])])).
% 1.81/2.00  cnf(c_0_129, negated_conjecture, (v4_tops_1(k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_106]), c_0_107]), c_0_58]), c_0_108])])).
% 1.81/2.00  cnf(c_0_130, plain, (k1_tops_1(X1,k2_tops_1(X2,X3))=k1_xboole_0|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(k1_tops_1(X1,k2_tops_1(X2,X3)),k1_tops_1(X2,X3))), inference(spm,[status(thm)],[c_0_124, c_0_51])).
% 1.81/2.00  cnf(c_0_131, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_125])).
% 1.81/2.00  cnf(c_0_132, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0)|~v4_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_83]), c_0_77]), c_0_58])])).
% 1.81/2.00  fof(c_0_133, plain, ![X26, X27]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|k2_tops_1(X26,X27)=k9_subset_1(u1_struct_0(X26),k2_pre_topc(X26,X27),k2_pre_topc(X26,k3_subset_1(u1_struct_0(X26),X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_1])])])).
% 1.81/2.00  cnf(c_0_134, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))=k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_102]), c_0_58]), c_0_57])])).
% 1.81/2.00  cnf(c_0_135, negated_conjecture, (k2_pre_topc(esk1_0,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))=k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_102]), c_0_58]), c_0_57])])).
% 1.81/2.00  cnf(c_0_136, negated_conjecture, (v4_tops_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_102]), c_0_58]), c_0_57])])).
% 1.81/2.00  cnf(c_0_137, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_102]), c_0_58]), c_0_57])])).
% 1.81/2.01  cnf(c_0_138, plain, (k1_tops_1(X1,k2_tops_1(X1,X2))=k1_xboole_0|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_tops_1(X1,X2),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_52]), c_0_131])).
% 1.81/2.01  fof(c_0_139, plain, ![X54, X55]:(~l1_pre_topc(X54)|(~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))|(~v4_pre_topc(X55,X54)|r1_tarski(k2_tops_1(X54,X55),X55)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_tops_1])])])).
% 1.81/2.01  cnf(c_0_140, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_98])])).
% 1.81/2.01  cnf(c_0_141, plain, (k2_tops_1(X1,X2)=k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_133])).
% 1.81/2.01  cnf(c_0_142, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_134]), c_0_107]), c_0_135]), c_0_136]), c_0_58]), c_0_137])])).
% 1.81/2.01  cnf(c_0_143, negated_conjecture, (k1_tops_1(esk1_0,k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)))=k1_xboole_0|~r1_tarski(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_95]), c_0_58])])).
% 1.81/2.01  cnf(c_0_144, plain, (r1_tarski(k2_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_139])).
% 1.81/2.01  cnf(c_0_145, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140, c_0_95])])).
% 1.81/2.01  cnf(c_0_146, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))=k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_113]), c_0_58])]), c_0_107]), c_0_142]), c_0_95])])).
% 1.81/2.01  cnf(c_0_147, negated_conjecture, (k1_tops_1(esk1_0,k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_145]), c_0_58]), c_0_95])])).
% 1.81/2.01  cnf(c_0_148, negated_conjecture, (k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_146]), c_0_58]), c_0_57])])).
% 1.81/2.01  cnf(c_0_149, negated_conjecture, (k1_tops_1(esk1_0,k2_tops_1(esk1_0,esk2_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.81/2.01  cnf(c_0_150, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_147, c_0_148]), c_0_149]), ['proof']).
% 1.81/2.01  # SZS output end CNFRefutation
% 1.81/2.01  # Proof object total steps             : 151
% 1.81/2.01  # Proof object clause steps            : 104
% 1.81/2.01  # Proof object formula steps           : 47
% 1.81/2.01  # Proof object conjectures             : 48
% 1.81/2.01  # Proof object clause conjectures      : 45
% 1.81/2.01  # Proof object formula conjectures     : 3
% 1.81/2.01  # Proof object initial clauses used    : 31
% 1.81/2.01  # Proof object initial formulas used   : 23
% 1.81/2.01  # Proof object generating inferences   : 64
% 1.81/2.01  # Proof object simplifying inferences  : 149
% 1.81/2.01  # Training examples: 0 positive, 0 negative
% 1.81/2.01  # Parsed axioms                        : 26
% 1.81/2.01  # Removed by relevancy pruning/SinE    : 0
% 1.81/2.01  # Initial clauses                      : 35
% 1.81/2.01  # Removed in clause preprocessing      : 0
% 1.81/2.01  # Initial clauses in saturation        : 35
% 1.81/2.01  # Processed clauses                    : 8345
% 1.81/2.01  # ...of these trivial                  : 199
% 1.81/2.01  # ...subsumed                          : 6073
% 1.81/2.01  # ...remaining for further processing  : 2073
% 1.81/2.01  # Other redundant clauses eliminated   : 2
% 1.81/2.01  # Clauses deleted for lack of memory   : 0
% 1.81/2.01  # Backward-subsumed                    : 307
% 1.81/2.01  # Backward-rewritten                   : 493
% 1.81/2.01  # Generated clauses                    : 56064
% 1.81/2.01  # ...of the previous two non-trivial   : 48261
% 1.81/2.01  # Contextual simplify-reflections      : 386
% 1.81/2.01  # Paramodulations                      : 56062
% 1.81/2.01  # Factorizations                       : 0
% 1.81/2.01  # Equation resolutions                 : 2
% 1.81/2.01  # Propositional unsat checks           : 0
% 1.81/2.01  #    Propositional check models        : 0
% 1.81/2.01  #    Propositional check unsatisfiable : 0
% 1.81/2.01  #    Propositional clauses             : 0
% 1.81/2.01  #    Propositional clauses after purity: 0
% 1.81/2.01  #    Propositional unsat core size     : 0
% 1.81/2.01  #    Propositional preprocessing time  : 0.000
% 1.81/2.01  #    Propositional encoding time       : 0.000
% 1.81/2.01  #    Propositional solver time         : 0.000
% 1.81/2.01  #    Success case prop preproc time    : 0.000
% 1.81/2.01  #    Success case prop encoding time   : 0.000
% 1.81/2.01  #    Success case prop solver time     : 0.000
% 1.81/2.01  # Current number of processed clauses  : 1237
% 1.81/2.01  #    Positive orientable unit clauses  : 85
% 1.81/2.01  #    Positive unorientable unit clauses: 0
% 1.81/2.01  #    Negative unit clauses             : 5
% 1.81/2.01  #    Non-unit-clauses                  : 1147
% 1.81/2.01  # Current number of unprocessed clauses: 38772
% 1.81/2.01  # ...number of literals in the above   : 241447
% 1.81/2.01  # Current number of archived formulas  : 0
% 1.81/2.01  # Current number of archived clauses   : 834
% 1.81/2.01  # Clause-clause subsumption calls (NU) : 245925
% 1.81/2.01  # Rec. Clause-clause subsumption calls : 68885
% 1.81/2.01  # Non-unit clause-clause subsumptions  : 6503
% 1.81/2.01  # Unit Clause-clause subsumption calls : 1116
% 1.81/2.01  # Rewrite failures with RHS unbound    : 0
% 1.81/2.01  # BW rewrite match attempts            : 106
% 1.81/2.01  # BW rewrite match successes           : 58
% 1.81/2.01  # Condensation attempts                : 0
% 1.81/2.01  # Condensation successes               : 0
% 1.81/2.01  # Termbank termtop insertions          : 2142291
% 1.81/2.01  
% 1.81/2.01  # -------------------------------------------------
% 1.81/2.01  # User time                : 1.625 s
% 1.81/2.01  # System time              : 0.040 s
% 1.81/2.01  # Total time               : 1.665 s
% 1.81/2.01  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
