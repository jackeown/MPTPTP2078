%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:51 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 213 expanded)
%              Number of clauses        :   43 (  78 expanded)
%              Number of leaves         :   15 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  219 (1137 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t24_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(fc1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_subset_1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ~ v1_xboole_0(k3_subset_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

fof(cc4_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ~ v1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | k3_subset_1(X7,X8) = k4_xboole_0(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & v3_tdlat_3(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( v3_pre_topc(esk3_0,esk2_0)
      | v4_pre_topc(esk3_0,esk2_0) )
    & v3_tex_2(esk3_0,esk2_0)
    & v1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_19,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk2_0),esk3_0) = k3_subset_1(u1_struct_0(esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | k3_subset_1(X9,k3_subset_1(X9,X10)) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

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

fof(c_0_26,plain,(
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

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
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

fof(c_0_31,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ v3_pre_topc(X31,X30)
      | ~ v3_tex_2(X31,X30)
      | v1_tops_1(X31,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).

cnf(c_0_32,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v3_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | v4_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_20])).

fof(c_0_40,plain,(
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

cnf(c_0_41,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( v3_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_20]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_35])])).

fof(c_0_47,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ v1_subset_1(X26,X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | ~ v1_xboole_0(k3_subset_1(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_tex_2])])])).

fof(c_0_48,plain,(
    ! [X12,X13] :
      ( ~ v1_xboole_0(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | ~ v1_subset_1(X13,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).

cnf(c_0_49,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) = u1_struct_0(esk2_0)
    | ~ v1_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_20]),c_0_35])])).

cnf(c_0_51,negated_conjecture,
    ( v1_tops_1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_20]),c_0_43]),c_0_44]),c_0_34]),c_0_35])]),c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_44])])).

fof(c_0_53,plain,(
    ! [X11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_54,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k3_subset_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) = esk3_0
    | ~ v4_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_20]),c_0_35])])).

cnf(c_0_58,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_59,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk2_0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_20]),c_0_35])])).

cnf(c_0_60,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_38]),c_0_33]),c_0_34]),c_0_35])]),c_0_52])])).

cnf(c_0_61,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( ~ v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(k3_subset_1(X2,X1)) ),
    inference(csr,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( esk3_0 = u1_struct_0(esk2_0)
    | ~ v4_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_67,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_61]),c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_20]),c_0_64])])).

cnf(c_0_69,negated_conjecture,
    ( esk3_0 = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_70,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_61]),c_0_67])).

cnf(c_0_71,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:52:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S2q
% 0.20/0.38  # and selection function SelectCQArNTNp.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t61_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((((v3_pre_topc(X2,X1)|v4_pre_topc(X2,X1))&v3_tex_2(X2,X1))&v1_subset_1(X2,u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 0.20/0.38  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.38  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.38  fof(t24_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 0.20/0.38  fof(t29_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 0.20/0.38  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 0.20/0.38  fof(t47_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_tex_2(X2,X1))=>v1_tops_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 0.20/0.38  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.38  fof(fc1_tex_2, axiom, ![X1, X2]:(((~(v1_xboole_0(X1))&v1_subset_1(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(X1)))=>~(v1_xboole_0(k3_subset_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tex_2)).
% 0.20/0.38  fof(cc4_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~(v1_subset_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 0.20/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.38  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((((v3_pre_topc(X2,X1)|v4_pre_topc(X2,X1))&v3_tex_2(X2,X1))&v1_subset_1(X2,u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t61_tex_2])).
% 0.20/0.38  fof(c_0_16, plain, ![X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|k3_subset_1(X7,X8)=k4_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.38  fof(c_0_17, negated_conjecture, ((((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&v3_tdlat_3(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((v3_pre_topc(esk3_0,esk2_0)|v4_pre_topc(esk3_0,esk2_0))&v3_tex_2(esk3_0,esk2_0))&v1_subset_1(esk3_0,u1_struct_0(esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.38  fof(c_0_18, plain, ![X4, X5]:r1_tarski(k4_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.38  cnf(c_0_19, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  fof(c_0_21, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.38  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (k4_xboole_0(u1_struct_0(esk2_0),esk3_0)=k3_subset_1(u1_struct_0(esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  fof(c_0_24, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|k3_subset_1(X9,k3_subset_1(X9,X10))=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.38  fof(c_0_25, plain, ![X27, X28]:((~v3_tdlat_3(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(~v4_pre_topc(X28,X27)|v3_pre_topc(X28,X27)))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&((m1_subset_1(esk1_1(X27),k1_zfmisc_1(u1_struct_0(X27)))|v3_tdlat_3(X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&((v4_pre_topc(esk1_1(X27),X27)|v3_tdlat_3(X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(~v3_pre_topc(esk1_1(X27),X27)|v3_tdlat_3(X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).
% 0.20/0.38  fof(c_0_26, plain, ![X21, X22]:((~v4_pre_topc(X22,X21)|v3_pre_topc(k3_subset_1(u1_struct_0(X21),X22),X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))&(~v3_pre_topc(k3_subset_1(u1_struct_0(X21),X22),X21)|v4_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).
% 0.20/0.38  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.38  cnf(c_0_29, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  fof(c_0_30, plain, ![X23, X24]:((~v1_tops_1(X24,X23)|k2_pre_topc(X23,X24)=u1_struct_0(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(k2_pre_topc(X23,X24)!=u1_struct_0(X23)|v1_tops_1(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 0.20/0.38  fof(c_0_31, plain, ![X30, X31]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(~v3_pre_topc(X31,X30)|~v3_tex_2(X31,X30)|v1_tops_1(X31,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_tex_2])])])])).
% 0.20/0.38  cnf(c_0_32, plain, (v3_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (v3_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|v4_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_37, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_29, c_0_20])).
% 0.20/0.38  fof(c_0_40, plain, ![X19, X20]:((~v4_pre_topc(X20,X19)|k2_pre_topc(X19,X20)=X20|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(~v2_pre_topc(X19)|k2_pre_topc(X19,X20)!=X20|v4_pre_topc(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.20/0.38  cnf(c_0_41, plain, (k2_pre_topc(X2,X1)=u1_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.38  cnf(c_0_42, plain, (v2_struct_0(X1)|v1_tops_1(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (v3_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_20]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (v4_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_35])])).
% 0.20/0.38  fof(c_0_47, plain, ![X25, X26]:(v1_xboole_0(X25)|~v1_subset_1(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(X25))|~v1_xboole_0(k3_subset_1(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_tex_2])])])).
% 0.20/0.38  fof(c_0_48, plain, ![X12, X13]:(~v1_xboole_0(X12)|(~m1_subset_1(X13,k1_zfmisc_1(X12))|~v1_subset_1(X13,X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_subset_1])])])])).
% 0.20/0.38  cnf(c_0_49, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)=u1_struct_0(esk2_0)|~v1_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_20]), c_0_35])])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (v1_tops_1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_20]), c_0_43]), c_0_44]), c_0_34]), c_0_35])]), c_0_45])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (v4_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_44])])).
% 0.20/0.38  fof(c_0_53, plain, ![X11]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.38  fof(c_0_54, plain, ![X6]:k4_xboole_0(X6,k1_xboole_0)=X6, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.38  cnf(c_0_55, plain, (v1_xboole_0(X1)|~v1_subset_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(k3_subset_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.38  cnf(c_0_56, plain, (~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)=esk3_0|~v4_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_20]), c_0_35])])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (v4_pre_topc(esk3_0,esk2_0)|~v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_20]), c_0_35])])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (v3_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_38]), c_0_33]), c_0_34]), c_0_35])]), c_0_52])])).
% 0.20/0.38  cnf(c_0_61, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.38  cnf(c_0_62, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.38  cnf(c_0_63, plain, (~v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(k3_subset_1(X2,X1))), inference(csr,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (esk3_0=u1_struct_0(esk2_0)|~v4_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (v4_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 0.20/0.38  cnf(c_0_67, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_61]), c_0_62])).
% 0.20/0.38  cnf(c_0_68, negated_conjecture, (~v1_xboole_0(k3_subset_1(u1_struct_0(esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_20]), c_0_64])])).
% 0.20/0.38  cnf(c_0_69, negated_conjecture, (esk3_0=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.20/0.38  cnf(c_0_70, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_61]), c_0_67])).
% 0.20/0.38  cnf(c_0_71, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.38  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 73
% 0.20/0.38  # Proof object clause steps            : 43
% 0.20/0.38  # Proof object formula steps           : 30
% 0.20/0.38  # Proof object conjectures             : 29
% 0.20/0.38  # Proof object clause conjectures      : 26
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 22
% 0.20/0.38  # Proof object initial formulas used   : 15
% 0.20/0.38  # Proof object generating inferences   : 14
% 0.20/0.38  # Proof object simplifying inferences  : 44
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 16
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 30
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 30
% 0.20/0.38  # Processed clauses                    : 105
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 4
% 0.20/0.38  # ...remaining for further processing  : 100
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 29
% 0.20/0.38  # Generated clauses                    : 81
% 0.20/0.38  # ...of the previous two non-trivial   : 92
% 0.20/0.38  # Contextual simplify-reflections      : 2
% 0.20/0.38  # Paramodulations                      : 81
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
% 0.20/0.38  # Current number of processed clauses  : 40
% 0.20/0.38  #    Positive orientable unit clauses  : 13
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 3
% 0.20/0.38  #    Non-unit-clauses                  : 23
% 0.20/0.38  # Current number of unprocessed clauses: 35
% 0.20/0.38  # ...number of literals in the above   : 109
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 60
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 379
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 58
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.20/0.38  # Unit Clause-clause subsumption calls : 36
% 0.20/0.38  # Rewrite failures with RHS unbound    : 3
% 0.20/0.38  # BW rewrite match attempts            : 26
% 0.20/0.38  # BW rewrite match successes           : 11
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3661
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
