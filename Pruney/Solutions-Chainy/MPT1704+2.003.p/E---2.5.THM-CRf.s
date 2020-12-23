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
% DateTime   : Thu Dec  3 11:16:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  119 (2139 expanded)
%              Number of clauses        :   77 ( 809 expanded)
%              Number of leaves         :   21 ( 553 expanded)
%              Depth                    :   19
%              Number of atoms          :  467 (14014 expanded)
%              Number of equality atoms :   53 (1232 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_tmap_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
               => ( ( v1_borsuk_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> ( v1_borsuk_1(X3,X1)
                    & m1_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t60_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v3_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(t61_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v4_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).

fof(cc2_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t11_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_borsuk_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).

fof(t12_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X2 = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
               => ( m1_pre_topc(X2,X1)
                <=> m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v2_pre_topc(X3)
                  & l1_pre_topc(X3) )
               => ( X3 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                 => ( ( v1_borsuk_1(X2,X1)
                      & m1_pre_topc(X2,X1) )
                  <=> ( v1_borsuk_1(X3,X1)
                      & m1_pre_topc(X3,X1) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_tmap_1])).

fof(c_0_22,plain,(
    ! [X17] : k2_subset_1(X17) = k3_subset_1(X17,k1_subset_1(X17)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_23,plain,(
    ! [X14] : k2_subset_1(X14) = X14 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_24,plain,(
    ! [X13] : k1_subset_1(X13) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_25,plain,(
    ! [X29,X30] :
      ( ( v3_pre_topc(X30,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))
        | ~ v3_pre_topc(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))))
        | ~ v3_pre_topc(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v3_pre_topc(X30,X29)
        | ~ v3_pre_topc(X30,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))))
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v3_pre_topc(X30,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))))
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).

fof(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & esk4_0 = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))
    & ( ~ v1_borsuk_1(esk3_0,esk2_0)
      | ~ m1_pre_topc(esk3_0,esk2_0)
      | ~ v1_borsuk_1(esk4_0,esk2_0)
      | ~ m1_pre_topc(esk4_0,esk2_0) )
    & ( v1_borsuk_1(esk4_0,esk2_0)
      | v1_borsuk_1(esk3_0,esk2_0) )
    & ( m1_pre_topc(esk4_0,esk2_0)
      | v1_borsuk_1(esk3_0,esk2_0) )
    & ( v1_borsuk_1(esk4_0,esk2_0)
      | m1_pre_topc(esk3_0,esk2_0) )
    & ( m1_pre_topc(esk4_0,esk2_0)
      | m1_pre_topc(esk3_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])).

fof(c_0_27,plain,(
    ! [X33,X34] :
      ( ( ~ v4_pre_topc(X34,X33)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X33),X34),X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_pre_topc(X33) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X33),X34),X33)
        | v4_pre_topc(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

cnf(c_0_28,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_32,plain,(
    ! [X15] : m1_subset_1(k2_subset_1(X15),k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_33,plain,(
    ! [X31,X32] :
      ( ( v4_pre_topc(X32,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))
        | ~ v4_pre_topc(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))))
        | ~ v4_pre_topc(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( v4_pre_topc(X32,X31)
        | ~ v4_pre_topc(X32,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ v4_pre_topc(X32,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_pre_topc])])])])).

fof(c_0_34,plain,(
    ! [X24,X25] :
      ( ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ v1_xboole_0(X25)
      | v4_pre_topc(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).

fof(c_0_35,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,X20)
      | v1_xboole_0(X20)
      | r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_36,plain,(
    ! [X16] : ~ v1_xboole_0(k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_43,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_48,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | m1_subset_1(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_53,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ v4_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_56,plain,
    ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_57,negated_conjecture,
    ( v4_pre_topc(X1,esk3_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_58,plain,
    ( v4_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_43])])).

cnf(c_0_59,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

fof(c_0_62,plain,(
    ! [X37,X38,X39] :
      ( ( ~ v1_borsuk_1(X38,X37)
        | ~ m1_pre_topc(X38,X37)
        | v4_pre_topc(X39,X37)
        | X39 != u1_struct_0(X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_pre_topc(X38,X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( v1_borsuk_1(X38,X37)
        | ~ v4_pre_topc(X39,X37)
        | X39 != u1_struct_0(X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_pre_topc(X38,X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( m1_pre_topc(X38,X37)
        | ~ v4_pre_topc(X39,X37)
        | X39 != u1_struct_0(X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_pre_topc(X38,X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tsep_1])])])])).

fof(c_0_63,plain,(
    ! [X40,X41,X42] :
      ( ( ~ m1_pre_topc(X41,X40)
        | m1_pre_topc(X42,X40)
        | X41 != g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | ~ l1_pre_topc(X40) )
      & ( ~ m1_pre_topc(X42,X40)
        | m1_pre_topc(X41,X40)
        | X41 != g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).

fof(c_0_64,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,X26)
      | l1_pre_topc(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v4_pre_topc(k1_xboole_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_66,negated_conjecture,
    ( v4_pre_topc(X1,esk4_0)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_67,negated_conjecture,
    ( v4_pre_topc(k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_43]),c_0_55]),c_0_59])])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_54])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_70,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v1_borsuk_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | X1 != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_73,plain,(
    ! [X6,X7,X8,X9,X10,X11] :
      ( ( ~ r2_hidden(X8,X7)
        | r1_tarski(X8,X6)
        | X7 != k1_zfmisc_1(X6) )
      & ( ~ r1_tarski(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k1_zfmisc_1(X6) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | ~ r1_tarski(esk1_2(X10,X11),X10)
        | X11 = k1_zfmisc_1(X10) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(esk1_2(X10,X11),X10)
        | X11 = k1_zfmisc_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_43])])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( v4_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_borsuk_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( v1_borsuk_1(esk4_0,esk2_0)
    | v1_borsuk_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_78,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_79,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_80,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0)
    | v1_borsuk_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_81,plain,(
    ! [X43,X44] :
      ( ~ l1_pre_topc(X43)
      | ~ m1_pre_topc(X44,X43)
      | m1_subset_1(u1_struct_0(X44),k1_zfmisc_1(u1_struct_0(X43))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_82,plain,
    ( m1_pre_topc(X1,X2)
    | X3 != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_71,c_0_72])).

fof(c_0_83,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_74]),c_0_51])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_53]),c_0_54]),c_0_67]),c_0_39])])).

cnf(c_0_87,negated_conjecture,
    ( v1_borsuk_1(esk3_0,esk2_0)
    | v4_pre_topc(X1,esk2_0)
    | X1 != u1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_79])]),c_0_80])).

cnf(c_0_88,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( m1_pre_topc(esk3_0,X1)
    | X2 != esk4_0
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_90,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0)
    | m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_91,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),X1)
    | k1_zfmisc_1(u1_struct_0(esk3_0)) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_86]),c_0_51])).

cnf(c_0_94,negated_conjecture,
    ( v1_borsuk_1(esk3_0,esk2_0)
    | v4_pre_topc(u1_struct_0(X1),esk2_0)
    | u1_struct_0(X1) != u1_struct_0(esk4_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_78])])).

cnf(c_0_95,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_78]),c_0_59])])).

cnf(c_0_96,negated_conjecture,
    ( X1 = u1_struct_0(esk4_0)
    | k1_zfmisc_1(u1_struct_0(esk3_0)) != k1_zfmisc_1(X1)
    | ~ r1_tarski(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),X1)
    | k1_zfmisc_1(u1_struct_0(esk4_0)) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( v1_borsuk_1(esk3_0,esk2_0)
    | v4_pre_topc(u1_struct_0(esk3_0),esk2_0)
    | u1_struct_0(esk4_0) != u1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( v1_borsuk_1(esk3_0,esk2_0)
    | v4_pre_topc(u1_struct_0(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_99])])).

fof(c_0_101,plain,(
    ! [X35,X36] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X36),u1_pre_topc(X36)))
        | ~ m1_pre_topc(X36,X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X36),u1_pre_topc(X36)),X35)
        | ~ m1_pre_topc(X36,X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

cnf(c_0_102,negated_conjecture,
    ( v4_pre_topc(u1_struct_0(esk3_0),esk2_0)
    | v4_pre_topc(X1,esk2_0)
    | X1 != u1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_100]),c_0_95]),c_0_78]),c_0_79])])).

cnf(c_0_103,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_104,negated_conjecture,
    ( v4_pre_topc(u1_struct_0(esk3_0),esk2_0)
    | v4_pre_topc(u1_struct_0(X1),esk2_0)
    | u1_struct_0(X1) != u1_struct_0(esk3_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_88]),c_0_78])])).

cnf(c_0_105,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_38])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_borsuk_1(esk3_0,esk2_0)
    | ~ m1_pre_topc(esk3_0,esk2_0)
    | ~ v1_borsuk_1(esk4_0,esk2_0)
    | ~ m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_107,plain,
    ( v1_borsuk_1(X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_108,negated_conjecture,
    ( v4_pre_topc(u1_struct_0(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_99]),c_0_99]),c_0_95]),c_0_78])])).

cnf(c_0_109,negated_conjecture,
    ( ~ v1_borsuk_1(esk3_0,esk2_0)
    | ~ v1_borsuk_1(esk4_0,esk2_0)
    | ~ m1_pre_topc(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_95])])).

cnf(c_0_110,negated_conjecture,
    ( v1_borsuk_1(X1,esk2_0)
    | u1_struct_0(esk3_0) != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_78]),c_0_79])])).

cnf(c_0_111,plain,
    ( m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_112,negated_conjecture,
    ( ~ v1_borsuk_1(esk3_0,esk2_0)
    | ~ m1_pre_topc(esk4_0,esk2_0)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_99])])).

cnf(c_0_113,plain,
    ( m1_pre_topc(X1,X2)
    | X1 != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_111,c_0_72])).

cnf(c_0_114,negated_conjecture,
    ( ~ m1_pre_topc(esk4_0,esk2_0)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_110]),c_0_95])])).

cnf(c_0_115,negated_conjecture,
    ( m1_pre_topc(X1,X2)
    | X1 != esk4_0
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_38]),c_0_40])])).

cnf(c_0_116,negated_conjecture,
    ( ~ m1_pre_topc(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_88]),c_0_95]),c_0_78])])).

cnf(c_0_117,negated_conjecture,
    ( m1_pre_topc(X1,esk2_0)
    | X1 != esk4_0
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_95]),c_0_78])])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_55]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:55:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.19/0.48  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.030 s
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t13_tmap_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X3=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>((v1_borsuk_1(X2,X1)&m1_pre_topc(X2,X1))<=>(v1_borsuk_1(X3,X1)&m1_pre_topc(X3,X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tmap_1)).
% 0.19/0.48  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.19/0.48  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.48  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.19/0.48  fof(t60_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v3_pre_topc(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 0.19/0.48  fof(t29_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 0.19/0.48  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.48  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.48  fof(t61_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v4_pre_topc(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_pre_topc)).
% 0.19/0.48  fof(cc2_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 0.19/0.48  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.48  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.48  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.48  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.48  fof(t11_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_borsuk_1(X2,X1)&m1_pre_topc(X2,X1))<=>v4_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tsep_1)).
% 0.19/0.48  fof(t12_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X2=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=>(m1_pre_topc(X2,X1)<=>m1_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 0.19/0.48  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.48  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.48  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.48  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.19/0.48  fof(c_0_21, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X3=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>((v1_borsuk_1(X2,X1)&m1_pre_topc(X2,X1))<=>(v1_borsuk_1(X3,X1)&m1_pre_topc(X3,X1)))))))), inference(assume_negation,[status(cth)],[t13_tmap_1])).
% 0.19/0.48  fof(c_0_22, plain, ![X17]:k2_subset_1(X17)=k3_subset_1(X17,k1_subset_1(X17)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.19/0.48  fof(c_0_23, plain, ![X14]:k2_subset_1(X14)=X14, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.48  fof(c_0_24, plain, ![X13]:k1_subset_1(X13)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.19/0.48  fof(c_0_25, plain, ![X29, X30]:(((v3_pre_topc(X30,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))|(~v3_pre_topc(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))))|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))))|(~v3_pre_topc(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))))|(~v2_pre_topc(X29)|~l1_pre_topc(X29))))&((v3_pre_topc(X30,X29)|(~v3_pre_topc(X30,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29))))))|(~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~v3_pre_topc(X30,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29))))))|(~v2_pre_topc(X29)|~l1_pre_topc(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).
% 0.19/0.48  fof(c_0_26, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&(esk4_0=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))&((~v1_borsuk_1(esk3_0,esk2_0)|~m1_pre_topc(esk3_0,esk2_0)|(~v1_borsuk_1(esk4_0,esk2_0)|~m1_pre_topc(esk4_0,esk2_0)))&(((v1_borsuk_1(esk4_0,esk2_0)|v1_borsuk_1(esk3_0,esk2_0))&(m1_pre_topc(esk4_0,esk2_0)|v1_borsuk_1(esk3_0,esk2_0)))&((v1_borsuk_1(esk4_0,esk2_0)|m1_pre_topc(esk3_0,esk2_0))&(m1_pre_topc(esk4_0,esk2_0)|m1_pre_topc(esk3_0,esk2_0))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])).
% 0.19/0.48  fof(c_0_27, plain, ![X33, X34]:((~v4_pre_topc(X34,X33)|v3_pre_topc(k3_subset_1(u1_struct_0(X33),X34),X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_pre_topc(X33))&(~v3_pre_topc(k3_subset_1(u1_struct_0(X33),X34),X33)|v4_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_pre_topc(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).
% 0.19/0.48  cnf(c_0_28, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.48  cnf(c_0_29, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.48  cnf(c_0_30, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.48  fof(c_0_31, plain, ![X18]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.48  fof(c_0_32, plain, ![X15]:m1_subset_1(k2_subset_1(X15),k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.48  fof(c_0_33, plain, ![X31, X32]:(((v4_pre_topc(X32,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))|(~v4_pre_topc(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))))|(~v4_pre_topc(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))|(~v2_pre_topc(X31)|~l1_pre_topc(X31))))&((v4_pre_topc(X32,X31)|(~v4_pre_topc(X32,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31))))))|(~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(~v4_pre_topc(X32,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31))))))|(~v2_pre_topc(X31)|~l1_pre_topc(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_pre_topc])])])])).
% 0.19/0.48  fof(c_0_34, plain, ![X24, X25]:(~v2_pre_topc(X24)|~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~v1_xboole_0(X25)|v4_pre_topc(X25,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).
% 0.19/0.48  fof(c_0_35, plain, ![X19, X20]:(~m1_subset_1(X19,X20)|(v1_xboole_0(X20)|r2_hidden(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.48  fof(c_0_36, plain, ![X16]:~v1_xboole_0(k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.48  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.48  cnf(c_0_38, negated_conjecture, (esk4_0=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_40, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_41, plain, (v3_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.48  cnf(c_0_42, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.19/0.48  cnf(c_0_43, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.48  cnf(c_0_44, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.48  cnf(c_0_45, plain, (v4_pre_topc(X1,X2)|~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.49  cnf(c_0_46, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.49  cnf(c_0_47, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.49  fof(c_0_48, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|m1_subset_1(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.49  cnf(c_0_49, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.49  cnf(c_0_50, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.49  cnf(c_0_51, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.49  cnf(c_0_52, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.19/0.49  cnf(c_0_53, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~v4_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.19/0.49  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_44, c_0_29])).
% 0.19/0.49  cnf(c_0_55, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.49  cnf(c_0_56, plain, (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.49  cnf(c_0_57, negated_conjecture, (v4_pre_topc(X1,esk3_0)|~v4_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_38]), c_0_39]), c_0_40])])).
% 0.19/0.49  cnf(c_0_58, plain, (v4_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_43])])).
% 0.19/0.49  cnf(c_0_59, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.49  cnf(c_0_60, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.49  cnf(c_0_61, plain, (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.49  fof(c_0_62, plain, ![X37, X38, X39]:((~v1_borsuk_1(X38,X37)|~m1_pre_topc(X38,X37)|v4_pre_topc(X39,X37)|X39!=u1_struct_0(X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|~m1_pre_topc(X38,X37)|(~v2_pre_topc(X37)|~l1_pre_topc(X37)))&((v1_borsuk_1(X38,X37)|~v4_pre_topc(X39,X37)|X39!=u1_struct_0(X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|~m1_pre_topc(X38,X37)|(~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(m1_pre_topc(X38,X37)|~v4_pre_topc(X39,X37)|X39!=u1_struct_0(X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|~m1_pre_topc(X38,X37)|(~v2_pre_topc(X37)|~l1_pre_topc(X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tsep_1])])])])).
% 0.19/0.49  fof(c_0_63, plain, ![X40, X41, X42]:((~m1_pre_topc(X41,X40)|m1_pre_topc(X42,X40)|X41!=g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))|(~v2_pre_topc(X42)|~l1_pre_topc(X42))|(~v2_pre_topc(X41)|~l1_pre_topc(X41))|~l1_pre_topc(X40))&(~m1_pre_topc(X42,X40)|m1_pre_topc(X41,X40)|X41!=g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))|(~v2_pre_topc(X42)|~l1_pre_topc(X42))|(~v2_pre_topc(X41)|~l1_pre_topc(X41))|~l1_pre_topc(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).
% 0.19/0.49  fof(c_0_64, plain, ![X26, X27]:(~l1_pre_topc(X26)|(~m1_pre_topc(X27,X26)|l1_pre_topc(X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.49  cnf(c_0_65, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~v4_pre_topc(k1_xboole_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55])])).
% 0.19/0.49  cnf(c_0_66, negated_conjecture, (v4_pre_topc(X1,esk4_0)|~v4_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_38]), c_0_39]), c_0_40])])).
% 0.19/0.49  cnf(c_0_67, negated_conjecture, (v4_pre_topc(k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_43]), c_0_55]), c_0_59])])).
% 0.19/0.49  cnf(c_0_68, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_60, c_0_54])).
% 0.19/0.49  cnf(c_0_69, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_38]), c_0_39]), c_0_40])])).
% 0.19/0.49  cnf(c_0_70, plain, (v4_pre_topc(X3,X2)|~v1_borsuk_1(X1,X2)|~m1_pre_topc(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.49  cnf(c_0_71, plain, (m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|X1!=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.49  cnf(c_0_72, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.49  fof(c_0_73, plain, ![X6, X7, X8, X9, X10, X11]:(((~r2_hidden(X8,X7)|r1_tarski(X8,X6)|X7!=k1_zfmisc_1(X6))&(~r1_tarski(X9,X6)|r2_hidden(X9,X7)|X7!=k1_zfmisc_1(X6)))&((~r2_hidden(esk1_2(X10,X11),X11)|~r1_tarski(esk1_2(X10,X11),X10)|X11=k1_zfmisc_1(X10))&(r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(esk1_2(X10,X11),X10)|X11=k1_zfmisc_1(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.49  cnf(c_0_74, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_43])])).
% 0.19/0.49  cnf(c_0_75, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.49  cnf(c_0_76, plain, (v4_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X1,X2)|~v1_borsuk_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[c_0_70])).
% 0.19/0.49  cnf(c_0_77, negated_conjecture, (v1_borsuk_1(esk4_0,esk2_0)|v1_borsuk_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.49  cnf(c_0_78, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.49  cnf(c_0_79, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.49  cnf(c_0_80, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)|v1_borsuk_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.49  fof(c_0_81, plain, ![X43, X44]:(~l1_pre_topc(X43)|(~m1_pre_topc(X44,X43)|m1_subset_1(u1_struct_0(X44),k1_zfmisc_1(u1_struct_0(X43))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.49  cnf(c_0_82, plain, (m1_pre_topc(X1,X2)|X3!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X3)), inference(csr,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.49  fof(c_0_83, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.49  cnf(c_0_84, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.49  cnf(c_0_85, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_74]), c_0_51])).
% 0.19/0.49  cnf(c_0_86, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_53]), c_0_54]), c_0_67]), c_0_39])])).
% 0.19/0.49  cnf(c_0_87, negated_conjecture, (v1_borsuk_1(esk3_0,esk2_0)|v4_pre_topc(X1,esk2_0)|X1!=u1_struct_0(esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_79])]), c_0_80])).
% 0.19/0.49  cnf(c_0_88, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.19/0.49  cnf(c_0_89, negated_conjecture, (m1_pre_topc(esk3_0,X1)|X2!=esk4_0|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_38]), c_0_39]), c_0_40])])).
% 0.19/0.49  cnf(c_0_90, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)|m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.49  cnf(c_0_91, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.19/0.49  cnf(c_0_92, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),X1)|k1_zfmisc_1(u1_struct_0(esk3_0))!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.49  cnf(c_0_93, negated_conjecture, (r2_hidden(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_86]), c_0_51])).
% 0.19/0.49  cnf(c_0_94, negated_conjecture, (v1_borsuk_1(esk3_0,esk2_0)|v4_pre_topc(u1_struct_0(X1),esk2_0)|u1_struct_0(X1)!=u1_struct_0(esk4_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_78])])).
% 0.19/0.49  cnf(c_0_95, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_78]), c_0_59])])).
% 0.19/0.49  cnf(c_0_96, negated_conjecture, (X1=u1_struct_0(esk4_0)|k1_zfmisc_1(u1_struct_0(esk3_0))!=k1_zfmisc_1(X1)|~r1_tarski(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.49  cnf(c_0_97, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),X1)|k1_zfmisc_1(u1_struct_0(esk4_0))!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_93])).
% 0.19/0.49  cnf(c_0_98, negated_conjecture, (v1_borsuk_1(esk3_0,esk2_0)|v4_pre_topc(u1_struct_0(esk3_0),esk2_0)|u1_struct_0(esk4_0)!=u1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.49  cnf(c_0_99, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.19/0.49  cnf(c_0_100, negated_conjecture, (v1_borsuk_1(esk3_0,esk2_0)|v4_pre_topc(u1_struct_0(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_99])])).
% 0.19/0.49  fof(c_0_101, plain, ![X35, X36]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X36),u1_pre_topc(X36)))|~m1_pre_topc(X36,X35)|~l1_pre_topc(X35))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X36),u1_pre_topc(X36)),X35)|~m1_pre_topc(X36,X35)|~l1_pre_topc(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.19/0.49  cnf(c_0_102, negated_conjecture, (v4_pre_topc(u1_struct_0(esk3_0),esk2_0)|v4_pre_topc(X1,esk2_0)|X1!=u1_struct_0(esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_100]), c_0_95]), c_0_78]), c_0_79])])).
% 0.19/0.49  cnf(c_0_103, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.19/0.49  cnf(c_0_104, negated_conjecture, (v4_pre_topc(u1_struct_0(esk3_0),esk2_0)|v4_pre_topc(u1_struct_0(X1),esk2_0)|u1_struct_0(X1)!=u1_struct_0(esk3_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_88]), c_0_78])])).
% 0.19/0.49  cnf(c_0_105, negated_conjecture, (m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_103, c_0_38])).
% 0.19/0.49  cnf(c_0_106, negated_conjecture, (~v1_borsuk_1(esk3_0,esk2_0)|~m1_pre_topc(esk3_0,esk2_0)|~v1_borsuk_1(esk4_0,esk2_0)|~m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.49  cnf(c_0_107, plain, (v1_borsuk_1(X1,X2)|~v4_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.49  cnf(c_0_108, negated_conjecture, (v4_pre_topc(u1_struct_0(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_99]), c_0_99]), c_0_95]), c_0_78])])).
% 0.19/0.49  cnf(c_0_109, negated_conjecture, (~v1_borsuk_1(esk3_0,esk2_0)|~v1_borsuk_1(esk4_0,esk2_0)|~m1_pre_topc(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_95])])).
% 0.19/0.49  cnf(c_0_110, negated_conjecture, (v1_borsuk_1(X1,esk2_0)|u1_struct_0(esk3_0)!=u1_struct_0(X1)|~m1_pre_topc(X1,esk2_0)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_78]), c_0_79])])).
% 0.19/0.49  cnf(c_0_111, plain, (m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|X3!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.49  cnf(c_0_112, negated_conjecture, (~v1_borsuk_1(esk3_0,esk2_0)|~m1_pre_topc(esk4_0,esk2_0)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_99])])).
% 0.19/0.49  cnf(c_0_113, plain, (m1_pre_topc(X1,X2)|X1!=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X3)), inference(csr,[status(thm)],[c_0_111, c_0_72])).
% 0.19/0.49  cnf(c_0_114, negated_conjecture, (~m1_pre_topc(esk4_0,esk2_0)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_110]), c_0_95])])).
% 0.19/0.49  cnf(c_0_115, negated_conjecture, (m1_pre_topc(X1,X2)|X1!=esk4_0|~m1_pre_topc(esk3_0,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_38]), c_0_40])])).
% 0.19/0.49  cnf(c_0_116, negated_conjecture, (~m1_pre_topc(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_88]), c_0_95]), c_0_78])])).
% 0.19/0.49  cnf(c_0_117, negated_conjecture, (m1_pre_topc(X1,esk2_0)|X1!=esk4_0|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_95]), c_0_78])])).
% 0.19/0.49  cnf(c_0_118, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_55]), c_0_59])]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 119
% 0.19/0.49  # Proof object clause steps            : 77
% 0.19/0.49  # Proof object formula steps           : 42
% 0.19/0.49  # Proof object conjectures             : 47
% 0.19/0.49  # Proof object clause conjectures      : 44
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 35
% 0.19/0.49  # Proof object initial formulas used   : 21
% 0.19/0.49  # Proof object generating inferences   : 35
% 0.19/0.49  # Proof object simplifying inferences  : 83
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 22
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 50
% 0.19/0.49  # Removed in clause preprocessing      : 3
% 0.19/0.49  # Initial clauses in saturation        : 47
% 0.19/0.49  # Processed clauses                    : 896
% 0.19/0.49  # ...of these trivial                  : 16
% 0.19/0.49  # ...subsumed                          : 319
% 0.19/0.49  # ...remaining for further processing  : 561
% 0.19/0.49  # Other redundant clauses eliminated   : 2
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 26
% 0.19/0.49  # Backward-rewritten                   : 107
% 0.19/0.49  # Generated clauses                    : 2117
% 0.19/0.49  # ...of the previous two non-trivial   : 1994
% 0.19/0.49  # Contextual simplify-reflections      : 20
% 0.19/0.49  # Paramodulations                      : 2052
% 0.19/0.49  # Factorizations                       : 6
% 0.19/0.49  # Equation resolutions                 : 58
% 0.19/0.49  # Propositional unsat checks           : 0
% 0.19/0.49  #    Propositional check models        : 0
% 0.19/0.49  #    Propositional check unsatisfiable : 0
% 0.19/0.49  #    Propositional clauses             : 0
% 0.19/0.49  #    Propositional clauses after purity: 0
% 0.19/0.49  #    Propositional unsat core size     : 0
% 0.19/0.49  #    Propositional preprocessing time  : 0.000
% 0.19/0.49  #    Propositional encoding time       : 0.000
% 0.19/0.49  #    Propositional solver time         : 0.000
% 0.19/0.49  #    Success case prop preproc time    : 0.000
% 0.19/0.49  #    Success case prop encoding time   : 0.000
% 0.19/0.49  #    Success case prop solver time     : 0.000
% 0.19/0.49  # Current number of processed clauses  : 425
% 0.19/0.49  #    Positive orientable unit clauses  : 34
% 0.19/0.49  #    Positive unorientable unit clauses: 0
% 0.19/0.49  #    Negative unit clauses             : 4
% 0.19/0.49  #    Non-unit-clauses                  : 387
% 0.19/0.49  # Current number of unprocessed clauses: 1070
% 0.19/0.49  # ...number of literals in the above   : 5789
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 136
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 31519
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 7752
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 334
% 0.19/0.49  # Unit Clause-clause subsumption calls : 484
% 0.19/0.49  # Rewrite failures with RHS unbound    : 0
% 0.19/0.49  # BW rewrite match attempts            : 95
% 0.19/0.49  # BW rewrite match successes           : 17
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 70128
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.142 s
% 0.19/0.49  # System time              : 0.006 s
% 0.19/0.49  # Total time               : 0.148 s
% 0.19/0.49  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
