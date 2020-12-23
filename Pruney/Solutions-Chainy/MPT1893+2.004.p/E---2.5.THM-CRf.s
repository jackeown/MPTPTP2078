%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:50 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 233 expanded)
%              Number of clauses        :   49 (  93 expanded)
%              Number of leaves         :   17 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  246 ( 951 expanded)
%              Number of equality atoms :   36 (  72 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ~ ( ( v3_pre_topc(X2,X1)
                | v4_pre_topc(X2,X1) )
              & v3_tex_2(X2,X1)
              & v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t47_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
              & v3_tex_2(X2,X1) )
           => v1_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

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

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

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

fof(fc1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_subset_1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ~ v1_xboole_0(k3_subset_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tex_2)).

fof(cc4_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ~ v1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ~ ( ( v3_pre_topc(X2,X1)
                  | v4_pre_topc(X2,X1) )
                & v3_tex_2(X2,X1)
                & v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_tex_2])).

fof(c_0_18,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,plain,(
    ! [X5,X6] : r1_tarski(k4_xboole_0(X5,X6),X5) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_20,plain,(
    ! [X3,X4] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,X3) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_21,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_22,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k1_xboole_0)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_23,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ v3_pre_topc(X31,X30)
      | ~ v3_tex_2(X31,X30)
      | v1_tops_1(X31,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & v3_tdlat_3(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( v3_pre_topc(esk3_0,esk2_0)
      | v4_pre_topc(esk3_0,esk2_0) )
    & v3_tex_2(esk3_0,esk2_0)
    & v1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_25,plain,(
    ! [X27,X28] :
      ( ( ~ v3_tdlat_3(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ v4_pre_topc(X28,X27)
        | v3_pre_topc(X28,X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( m1_subset_1(esk1_1(X27),k1_zfmisc_1(u1_struct_0(X27)))
        | v3_tdlat_3(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( v4_pre_topc(esk1_1(X27),X27)
        | v3_tdlat_3(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ v3_pre_topc(esk1_1(X27),X27)
        | v3_tdlat_3(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | k3_subset_1(X11,X12) = k4_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_33,plain,(
    ! [X23,X24] :
      ( ( ~ v1_tops_1(X24,X23)
        | k2_pre_topc(X23,X24) = u1_struct_0(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( k2_pre_topc(X23,X24) != u1_struct_0(X23)
        | v1_tops_1(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( v3_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_40,plain,(
    ! [X21,X22] :
      ( ( ~ v4_pre_topc(X22,X21)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X21),X22),X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X21),X22),X21)
        | v4_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

cnf(c_0_41,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( v3_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_43,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_44,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_45,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | k3_subset_1(X13,k3_subset_1(X13,X14)) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_30])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_49,plain,(
    ! [X19,X20] :
      ( ( ~ v4_pre_topc(X20,X19)
        | k2_pre_topc(X19,X20) = X20
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ v2_pre_topc(X19)
        | k2_pre_topc(X19,X20) != X20
        | v4_pre_topc(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_50,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( v1_tops_1(esk3_0,esk2_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_52,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_36]),c_0_37])])).

cnf(c_0_54,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_55,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_56,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ v1_subset_1(X26,X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | ~ v1_xboole_0(k3_subset_1(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_tex_2])])])).

fof(c_0_57,plain,(
    ! [X15,X16] :
      ( ~ v1_xboole_0(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | ~ v1_subset_1(X16,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_59,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) = u1_struct_0(esk2_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_37]),c_0_38])])).

cnf(c_0_61,negated_conjecture,
    ( v4_pre_topc(X1,esk2_0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(esk2_0),X1),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_37])]),c_0_54])).

cnf(c_0_62,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_55]),c_0_54])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k3_subset_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ v4_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_37]),c_0_38])])).

cnf(c_0_67,negated_conjecture,
    ( v4_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_37])])).

cnf(c_0_68,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | v4_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_69,plain,
    ( ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(k3_subset_1(X2,X1)) ),
    inference(csr,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_44])).

cnf(c_0_71,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_65])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_48])).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0
    | ~ v4_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_53]),c_0_38])])).

cnf(c_0_74,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_38])])).

cnf(c_0_75,plain,
    ( ~ v1_subset_1(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_55])).

cnf(c_0_76,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_72])).

cnf(c_0_78,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_79,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_81,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_71]),c_0_78])])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_RG_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t61_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((((v3_pre_topc(X2,X1)|v4_pre_topc(X2,X1))&v3_tex_2(X2,X1))&v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 0.20/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.38  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.38  fof(t47_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tex_2(X2,X1))=>v1_tops_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 0.20/0.38  fof(t24_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 0.20/0.38  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.38  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 0.20/0.38  fof(t29_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 0.20/0.38  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.38  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.38  fof(fc1_tex_2, axiom, ![X1, X2]:(((~(v1_xboole_0(X1))&v1_subset_1(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(X1)))=>~(v1_xboole_0(k3_subset_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tex_2)).
% 0.20/0.38  fof(cc4_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~(v1_subset_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 0.20/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((((v3_pre_topc(X2,X1)|v4_pre_topc(X2,X1))&v3_tex_2(X2,X1))&v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t61_tex_2])).
% 0.20/0.38  fof(c_0_18, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.38  fof(c_0_19, plain, ![X5, X6]:r1_tarski(k4_xboole_0(X5,X6),X5), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.38  fof(c_0_20, plain, ![X3, X4]:k3_xboole_0(X3,X4)=k3_xboole_0(X4,X3), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.38  fof(c_0_21, plain, ![X9, X10]:k4_xboole_0(X9,k4_xboole_0(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.38  fof(c_0_22, plain, ![X8]:(~r1_tarski(X8,k1_xboole_0)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.38  fof(c_0_23, plain, ![X30, X31]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(~v3_pre_topc(X31,X30)|~v3_tex_2(X31,X30)|v1_tops_1(X31,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).
% 0.20/0.38  fof(c_0_24, negated_conjecture, ((((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&v3_tdlat_3(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((v3_pre_topc(esk3_0,esk2_0)|v4_pre_topc(esk3_0,esk2_0))&v3_tex_2(esk3_0,esk2_0))&v1_subset_1(esk3_0,u1_struct_0(esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.20/0.38  fof(c_0_25, plain, ![X27, X28]:((~v3_tdlat_3(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(~v4_pre_topc(X28,X27)|v3_pre_topc(X28,X27)))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&((m1_subset_1(esk1_1(X27),k1_zfmisc_1(u1_struct_0(X27)))|v3_tdlat_3(X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&((v4_pre_topc(esk1_1(X27),X27)|v3_tdlat_3(X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(~v3_pre_topc(esk1_1(X27),X27)|v3_tdlat_3(X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).
% 0.20/0.38  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_27, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_28, plain, ![X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|k3_subset_1(X11,X12)=k4_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.38  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_31, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  fof(c_0_32, plain, ![X7]:k4_xboole_0(X7,k1_xboole_0)=X7, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.38  fof(c_0_33, plain, ![X23, X24]:((~v1_tops_1(X24,X23)|k2_pre_topc(X23,X24)=u1_struct_0(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(k2_pre_topc(X23,X24)!=u1_struct_0(X23)|v1_tops_1(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 0.20/0.38  cnf(c_0_34, plain, (v2_struct_0(X1)|v1_tops_1(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (v3_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  fof(c_0_40, plain, ![X21, X22]:((~v4_pre_topc(X22,X21)|v3_pre_topc(k3_subset_1(u1_struct_0(X21),X22),X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))&(~v3_pre_topc(k3_subset_1(u1_struct_0(X21),X22),X21)|v4_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).
% 0.20/0.38  cnf(c_0_41, plain, (v3_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (v3_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_43, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.38  cnf(c_0_44, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  fof(c_0_45, plain, ![X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|k3_subset_1(X13,k3_subset_1(X13,X14))=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.38  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_30])).
% 0.20/0.38  cnf(c_0_47, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 0.20/0.38  cnf(c_0_48, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  fof(c_0_49, plain, ![X19, X20]:((~v4_pre_topc(X20,X19)|k2_pre_topc(X19,X20)=X20|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(~v2_pre_topc(X19)|k2_pre_topc(X19,X20)!=X20|v4_pre_topc(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.20/0.38  cnf(c_0_50, plain, (k2_pre_topc(X2,X1)=u1_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (v1_tops_1(esk3_0,esk2_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38])]), c_0_39])).
% 0.20/0.38  cnf(c_0_52, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~v4_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_36]), c_0_37])])).
% 0.20/0.38  cnf(c_0_54, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.38  cnf(c_0_55, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.38  fof(c_0_56, plain, ![X25, X26]:(v1_xboole_0(X25)|~v1_subset_1(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(X25))|~v1_xboole_0(k3_subset_1(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_tex_2])])])).
% 0.20/0.38  fof(c_0_57, plain, ![X15, X16]:(~v1_xboole_0(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|~v1_subset_1(X16,X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).
% 0.20/0.38  cnf(c_0_58, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.20/0.38  cnf(c_0_59, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)=u1_struct_0(esk2_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_37]), c_0_38])])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (v4_pre_topc(X1,esk2_0)|~v4_pre_topc(k3_subset_1(u1_struct_0(esk2_0),X1),esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_37])]), c_0_54])).
% 0.20/0.38  cnf(c_0_62, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_55]), c_0_54])).
% 0.20/0.38  cnf(c_0_63, plain, (v1_xboole_0(X1)|~v1_subset_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(k3_subset_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.38  cnf(c_0_64, plain, (~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.38  cnf(c_0_65, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_58])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0|~v3_pre_topc(esk3_0,esk2_0)|~v4_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_37]), c_0_38])])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, (v4_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_37])])).
% 0.20/0.38  cnf(c_0_68, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|v4_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_69, plain, (~v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(k3_subset_1(X2,X1))), inference(csr,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.38  cnf(c_0_70, plain, (k3_subset_1(X1,k1_xboole_0)=X1|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_44])).
% 0.20/0.38  cnf(c_0_71, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_65])).
% 0.20/0.38  cnf(c_0_72, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_27, c_0_48])).
% 0.20/0.38  cnf(c_0_73, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0|~v4_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_53]), c_0_38])])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (v4_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_38])])).
% 0.20/0.38  cnf(c_0_75, plain, (~v1_subset_1(k3_subset_1(X1,X2),X1)|~m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_69, c_0_55])).
% 0.20/0.38  cnf(c_0_76, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])])).
% 0.20/0.38  cnf(c_0_77, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_72])).
% 0.20/0.38  cnf(c_0_78, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.38  cnf(c_0_79, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_80, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])])).
% 0.20/0.38  cnf(c_0_81, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_71]), c_0_78])])).
% 0.20/0.38  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_81]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 83
% 0.20/0.38  # Proof object clause steps            : 49
% 0.20/0.38  # Proof object formula steps           : 34
% 0.20/0.38  # Proof object conjectures             : 21
% 0.20/0.38  # Proof object clause conjectures      : 18
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 24
% 0.20/0.38  # Proof object initial formulas used   : 17
% 0.20/0.38  # Proof object generating inferences   : 20
% 0.20/0.38  # Proof object simplifying inferences  : 38
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 17
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 31
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 30
% 0.20/0.38  # Processed clauses                    : 76
% 0.20/0.38  # ...of these trivial                  : 4
% 0.20/0.38  # ...subsumed                          : 6
% 0.20/0.38  # ...remaining for further processing  : 66
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 11
% 0.20/0.38  # Generated clauses                    : 133
% 0.20/0.38  # ...of the previous two non-trivial   : 103
% 0.20/0.38  # Contextual simplify-reflections      : 4
% 0.20/0.38  # Paramodulations                      : 133
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 53
% 0.20/0.38  #    Positive orientable unit clauses  : 18
% 0.20/0.38  #    Positive unorientable unit clauses: 2
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 31
% 0.20/0.38  # Current number of unprocessed clauses: 49
% 0.20/0.38  # ...number of literals in the above   : 97
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 14
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 362
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 107
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.20/0.38  # Unit Clause-clause subsumption calls : 51
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 23
% 0.20/0.38  # BW rewrite match successes           : 5
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3942
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.031 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
