%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:33 EST 2020

% Result     : Theorem 33.47s
% Output     : CNFRefutation 33.47s
% Verified   : 
% Statistics : Number of formulae       :  113 (15604 expanded)
%              Number of clauses        :   72 (7432 expanded)
%              Number of leaves         :   20 (4071 expanded)
%              Depth                    :   22
%              Number of atoms          :  251 (26353 expanded)
%              Number of equality atoms :   79 (14250 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t29_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d6_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(c_0_20,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X48,X49] : k1_setfam_1(k2_tarski(X48,X49)) = k3_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_22,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_27,plain,(
    ! [X27,X28] : k2_tarski(X27,X28) = k2_tarski(X28,X27) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_28,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | k3_subset_1(X33,X34) = k4_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_29,plain,(
    ! [X35] : m1_subset_1(k2_subset_1(X35),k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_30,plain,(
    ! [X32] : k2_subset_1(X32) = X32 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_31,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X24] : k4_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_37,plain,
    ( X1 != k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_41,plain,(
    ! [X47] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X47)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_42,plain,
    ( X1 != k3_subset_1(X2,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_40,c_0_26])).

cnf(c_0_44,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k3_subset_1(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_38]),c_0_44])])).

fof(c_0_48,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_45,c_0_26])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

fof(c_0_51,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_52,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( X1 != k3_subset_1(X2,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_39])]),c_0_42])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k3_subset_1(X2,X2)) ),
    inference(er,[status(thm)],[c_0_55])).

fof(c_0_60,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X41))
      | k9_subset_1(X41,X42,X43) = k3_xboole_0(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_61,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tops_1])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_24]),c_0_26]),c_0_26])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_54])).

fof(c_0_65,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X44))
      | ~ m1_subset_1(X46,k1_zfmisc_1(X44))
      | k7_subset_1(X44,X45,X46) = k9_subset_1(X44,X45,k3_subset_1(X44,X46)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

cnf(c_0_66,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_67,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | m1_subset_1(k3_subset_1(X36,X37),k1_zfmisc_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_68,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | ~ r2_hidden(X40,X39)
      | r2_hidden(X40,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_69,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v4_pre_topc(esk4_0,esk3_0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0) )
    & ( v4_pre_topc(esk4_0,esk3_0)
      | v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_61])])])).

cnf(c_0_70,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2))
    | ~ m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_62])).

cnf(c_0_71,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_24])).

cnf(c_0_74,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_76,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_43]),c_0_71]),c_0_39])])).

cnf(c_0_79,plain,
    ( k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,X3))) = k7_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_80,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_75,c_0_26])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_83,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_32])).

cnf(c_0_84,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k7_subset_1(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_47]),c_0_44])])).

cnf(c_0_85,negated_conjecture,
    ( X1 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,u1_struct_0(esk3_0))))
    | r2_hidden(esk2_3(X2,u1_struct_0(esk3_0),X1),X1)
    | ~ r2_hidden(esk2_3(X2,u1_struct_0(esk3_0),X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_82,c_0_26])).

cnf(c_0_87,plain,
    ( k7_subset_1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_44])])).

cnf(c_0_88,negated_conjecture,
    ( X1 = k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))
    | r2_hidden(esk2_3(esk4_0,u1_struct_0(esk3_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_87]),c_0_87]),c_0_53])).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_43,c_0_78])).

fof(c_0_91,plain,(
    ! [X53] :
      ( ~ l1_struct_0(X53)
      | k2_struct_0(X53) = u1_struct_0(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_92,plain,(
    ! [X56] :
      ( ~ l1_pre_topc(X56)
      | l1_struct_0(X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))) = k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_62])).

cnf(c_0_94,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_89]),c_0_78]),c_0_90])).

fof(c_0_95,plain,(
    ! [X54,X55] :
      ( ( ~ v4_pre_topc(X55,X54)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X54),k2_struct_0(X54),X55),X54)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
        | ~ l1_pre_topc(X54) )
      & ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X54),k2_struct_0(X54),X55),X54)
        | v4_pre_topc(X55,X54)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
        | ~ l1_pre_topc(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).

cnf(c_0_96,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_97,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X1))))) = k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_32])).

cnf(c_0_99,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk3_0),esk4_0) = k3_subset_1(u1_struct_0(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_94]),c_0_77])])).

cnf(c_0_100,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_101,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( k1_setfam_1(k2_tarski(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0))) = k3_subset_1(u1_struct_0(esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_94]),c_0_32]),c_0_94]),c_0_99]),c_0_99])).

cnf(c_0_103,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_104,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X2),u1_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),esk4_0) = k3_subset_1(u1_struct_0(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_102]),c_0_77]),c_0_39])])).

cnf(c_0_106,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_107,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk3_0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_108,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_101])).

cnf(c_0_109,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106]),c_0_77])]),c_0_107])).

cnf(c_0_110,negated_conjecture,
    ( ~ v4_pre_topc(esk4_0,esk3_0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_111,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_105]),c_0_106]),c_0_77])]),c_0_109])])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_109])]),c_0_111])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:08:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 33.47/33.70  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 33.47/33.70  # and selection function PSelectComplexExceptUniqMaxHorn.
% 33.47/33.70  #
% 33.47/33.70  # Preprocessing time       : 0.029 s
% 33.47/33.70  
% 33.47/33.70  # Proof found!
% 33.47/33.70  # SZS status Theorem
% 33.47/33.70  # SZS output start CNFRefutation
% 33.47/33.70  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 33.47/33.70  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 33.47/33.70  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 33.47/33.70  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 33.47/33.70  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 33.47/33.70  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 33.47/33.70  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 33.47/33.70  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 33.47/33.70  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 33.47/33.70  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 33.47/33.70  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 33.47/33.70  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 33.47/33.70  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 33.47/33.70  fof(t29_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 33.47/33.70  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 33.47/33.70  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 33.47/33.70  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 33.47/33.70  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 33.47/33.70  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 33.47/33.70  fof(d6_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 33.47/33.70  fof(c_0_20, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 33.47/33.70  fof(c_0_21, plain, ![X48, X49]:k1_setfam_1(k2_tarski(X48,X49))=k3_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 33.47/33.70  fof(c_0_22, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 33.47/33.70  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 33.47/33.70  cnf(c_0_24, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 33.47/33.70  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 33.47/33.70  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 33.47/33.70  fof(c_0_27, plain, ![X27, X28]:k2_tarski(X27,X28)=k2_tarski(X28,X27), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 33.47/33.70  fof(c_0_28, plain, ![X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|k3_subset_1(X33,X34)=k4_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 33.47/33.70  fof(c_0_29, plain, ![X35]:m1_subset_1(k2_subset_1(X35),k1_zfmisc_1(X35)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 33.47/33.70  fof(c_0_30, plain, ![X32]:k2_subset_1(X32)=X32, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 33.47/33.70  cnf(c_0_31, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 33.47/33.70  cnf(c_0_32, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 33.47/33.70  cnf(c_0_33, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 33.47/33.70  cnf(c_0_34, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 33.47/33.70  cnf(c_0_35, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 33.47/33.70  fof(c_0_36, plain, ![X24]:k4_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t3_boole])).
% 33.47/33.70  cnf(c_0_37, plain, (X1!=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))|~r2_hidden(X4,X1)|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 33.47/33.70  cnf(c_0_38, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_33, c_0_26])).
% 33.47/33.70  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 33.47/33.70  cnf(c_0_40, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 33.47/33.70  fof(c_0_41, plain, ![X47]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X47)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 33.47/33.70  cnf(c_0_42, plain, (X1!=k3_subset_1(X2,X2)|~r2_hidden(X3,X1)|~r2_hidden(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 33.47/33.70  cnf(c_0_43, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_40, c_0_26])).
% 33.47/33.70  cnf(c_0_44, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 33.47/33.70  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 33.47/33.70  cnf(c_0_46, plain, (~r2_hidden(X1,k3_subset_1(X2,X2))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_42])).
% 33.47/33.70  cnf(c_0_47, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_38]), c_0_44])])).
% 33.47/33.70  fof(c_0_48, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 33.47/33.70  cnf(c_0_49, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_45, c_0_26])).
% 33.47/33.70  cnf(c_0_50, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_32])).
% 33.47/33.70  fof(c_0_51, plain, ![X25, X26]:k4_xboole_0(X25,k4_xboole_0(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 33.47/33.70  fof(c_0_52, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 33.47/33.70  cnf(c_0_53, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 33.47/33.70  cnf(c_0_54, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 33.47/33.70  cnf(c_0_55, plain, (X1!=k3_subset_1(X2,X2)|~r2_hidden(X3,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_39])]), c_0_42])).
% 33.47/33.70  cnf(c_0_56, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 33.47/33.70  cnf(c_0_57, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 33.47/33.70  cnf(c_0_58, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 33.47/33.70  cnf(c_0_59, plain, (~r2_hidden(X1,k3_subset_1(X2,X2))), inference(er,[status(thm)],[c_0_55])).
% 33.47/33.70  fof(c_0_60, plain, ![X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(X41))|k9_subset_1(X41,X42,X43)=k3_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 33.47/33.70  fof(c_0_61, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t29_tops_1])).
% 33.47/33.70  cnf(c_0_62, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_24]), c_0_26]), c_0_26])).
% 33.47/33.70  cnf(c_0_63, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 33.47/33.70  cnf(c_0_64, plain, (r1_tarski(k3_subset_1(X1,X1),X2)), inference(spm,[status(thm)],[c_0_59, c_0_54])).
% 33.47/33.70  fof(c_0_65, plain, ![X44, X45, X46]:(~m1_subset_1(X45,k1_zfmisc_1(X44))|(~m1_subset_1(X46,k1_zfmisc_1(X44))|k7_subset_1(X44,X45,X46)=k9_subset_1(X44,X45,k3_subset_1(X44,X46)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 33.47/33.70  cnf(c_0_66, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 33.47/33.70  fof(c_0_67, plain, ![X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|m1_subset_1(k3_subset_1(X36,X37),k1_zfmisc_1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 33.47/33.70  fof(c_0_68, plain, ![X38, X39, X40]:(~m1_subset_1(X39,k1_zfmisc_1(X38))|(~r2_hidden(X40,X39)|r2_hidden(X40,X38))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 33.47/33.70  fof(c_0_69, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v4_pre_topc(esk4_0,esk3_0)|~v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0))&(v4_pre_topc(esk4_0,esk3_0)|v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_61])])])).
% 33.47/33.70  cnf(c_0_70, plain, (k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))|~m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_62])).
% 33.47/33.70  cnf(c_0_71, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 33.47/33.70  cnf(c_0_72, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 33.47/33.70  cnf(c_0_73, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_66, c_0_24])).
% 33.47/33.70  cnf(c_0_74, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 33.47/33.70  cnf(c_0_75, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 33.47/33.70  cnf(c_0_76, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 33.47/33.70  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 33.47/33.70  cnf(c_0_78, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_43]), c_0_71]), c_0_39])])).
% 33.47/33.70  cnf(c_0_79, plain, (k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,X3)))=k7_subset_1(X2,X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 33.47/33.70  cnf(c_0_80, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_75, c_0_26])).
% 33.47/33.70  cnf(c_0_81, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 33.47/33.70  cnf(c_0_82, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 33.47/33.70  cnf(c_0_83, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_32])).
% 33.47/33.70  cnf(c_0_84, plain, (k1_setfam_1(k2_tarski(X1,X2))=k7_subset_1(X2,X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_47]), c_0_44])])).
% 33.47/33.70  cnf(c_0_85, negated_conjecture, (X1=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,u1_struct_0(esk3_0))))|r2_hidden(esk2_3(X2,u1_struct_0(esk3_0),X1),X1)|~r2_hidden(esk2_3(X2,u1_struct_0(esk3_0),X1),esk4_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 33.47/33.70  cnf(c_0_86, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_82, c_0_26])).
% 33.47/33.70  cnf(c_0_87, plain, (k7_subset_1(X1,k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_44])])).
% 33.47/33.70  cnf(c_0_88, negated_conjecture, (X1=k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))|r2_hidden(esk2_3(esk4_0,u1_struct_0(esk3_0),X1),X1)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 33.47/33.70  cnf(c_0_89, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_87]), c_0_87]), c_0_53])).
% 33.47/33.70  cnf(c_0_90, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_43, c_0_78])).
% 33.47/33.70  fof(c_0_91, plain, ![X53]:(~l1_struct_0(X53)|k2_struct_0(X53)=u1_struct_0(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 33.47/33.70  fof(c_0_92, plain, ![X56]:(~l1_pre_topc(X56)|l1_struct_0(X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 33.47/33.70  cnf(c_0_93, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))))=k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))), inference(spm,[status(thm)],[c_0_62, c_0_62])).
% 33.47/33.70  cnf(c_0_94, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_89]), c_0_78]), c_0_90])).
% 33.47/33.70  fof(c_0_95, plain, ![X54, X55]:((~v4_pre_topc(X55,X54)|v3_pre_topc(k7_subset_1(u1_struct_0(X54),k2_struct_0(X54),X55),X54)|~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))|~l1_pre_topc(X54))&(~v3_pre_topc(k7_subset_1(u1_struct_0(X54),k2_struct_0(X54),X55),X54)|v4_pre_topc(X55,X54)|~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))|~l1_pre_topc(X54))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).
% 33.47/33.70  cnf(c_0_96, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 33.47/33.70  cnf(c_0_97, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 33.47/33.70  cnf(c_0_98, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X1)))))=k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))))), inference(spm,[status(thm)],[c_0_93, c_0_32])).
% 33.47/33.70  cnf(c_0_99, negated_conjecture, (k5_xboole_0(u1_struct_0(esk3_0),esk4_0)=k3_subset_1(u1_struct_0(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_94]), c_0_77])])).
% 33.47/33.70  cnf(c_0_100, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 33.47/33.70  cnf(c_0_101, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 33.47/33.70  cnf(c_0_102, negated_conjecture, (k1_setfam_1(k2_tarski(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0)))=k3_subset_1(u1_struct_0(esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_94]), c_0_32]), c_0_94]), c_0_99]), c_0_99])).
% 33.47/33.70  cnf(c_0_103, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 33.47/33.70  cnf(c_0_104, plain, (v4_pre_topc(X1,X2)|~v3_pre_topc(k7_subset_1(u1_struct_0(X2),u1_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 33.47/33.70  cnf(c_0_105, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),esk4_0)=k3_subset_1(u1_struct_0(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_102]), c_0_77]), c_0_39])])).
% 33.47/33.70  cnf(c_0_106, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 33.47/33.70  cnf(c_0_107, negated_conjecture, (v4_pre_topc(esk4_0,esk3_0)|v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 33.47/33.70  cnf(c_0_108, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)|~v4_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_103, c_0_101])).
% 33.47/33.70  cnf(c_0_109, negated_conjecture, (v4_pre_topc(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106]), c_0_77])]), c_0_107])).
% 33.47/33.70  cnf(c_0_110, negated_conjecture, (~v4_pre_topc(esk4_0,esk3_0)|~v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 33.47/33.70  cnf(c_0_111, negated_conjecture, (v3_pre_topc(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_105]), c_0_106]), c_0_77])]), c_0_109])])).
% 33.47/33.70  cnf(c_0_112, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_109])]), c_0_111])]), ['proof']).
% 33.47/33.70  # SZS output end CNFRefutation
% 33.47/33.70  # Proof object total steps             : 113
% 33.47/33.70  # Proof object clause steps            : 72
% 33.47/33.70  # Proof object formula steps           : 41
% 33.47/33.70  # Proof object conjectures             : 18
% 33.47/33.70  # Proof object clause conjectures      : 15
% 33.47/33.70  # Proof object formula conjectures     : 3
% 33.47/33.70  # Proof object initial clauses used    : 27
% 33.47/33.70  # Proof object initial formulas used   : 20
% 33.47/33.70  # Proof object generating inferences   : 33
% 33.47/33.70  # Proof object simplifying inferences  : 55
% 33.47/33.70  # Training examples: 0 positive, 0 negative
% 33.47/33.70  # Parsed axioms                        : 22
% 33.47/33.70  # Removed by relevancy pruning/SinE    : 0
% 33.47/33.70  # Initial clauses                      : 35
% 33.47/33.70  # Removed in clause preprocessing      : 3
% 33.47/33.70  # Initial clauses in saturation        : 32
% 33.47/33.70  # Processed clauses                    : 13573
% 33.47/33.70  # ...of these trivial                  : 461
% 33.47/33.70  # ...subsumed                          : 10388
% 33.47/33.70  # ...remaining for further processing  : 2723
% 33.47/33.70  # Other redundant clauses eliminated   : 8854
% 33.47/33.70  # Clauses deleted for lack of memory   : 0
% 33.47/33.70  # Backward-subsumed                    : 203
% 33.47/33.70  # Backward-rewritten                   : 402
% 33.47/33.70  # Generated clauses                    : 1565572
% 33.47/33.70  # ...of the previous two non-trivial   : 1533292
% 33.47/33.70  # Contextual simplify-reflections      : 172
% 33.47/33.70  # Paramodulations                      : 1552878
% 33.47/33.70  # Factorizations                       : 3615
% 33.47/33.70  # Equation resolutions                 : 9074
% 33.47/33.70  # Propositional unsat checks           : 0
% 33.47/33.70  #    Propositional check models        : 0
% 33.47/33.70  #    Propositional check unsatisfiable : 0
% 33.47/33.70  #    Propositional clauses             : 0
% 33.47/33.70  #    Propositional clauses after purity: 0
% 33.47/33.70  #    Propositional unsat core size     : 0
% 33.47/33.70  #    Propositional preprocessing time  : 0.000
% 33.47/33.70  #    Propositional encoding time       : 0.000
% 33.47/33.70  #    Propositional solver time         : 0.000
% 33.47/33.70  #    Success case prop preproc time    : 0.000
% 33.47/33.70  #    Success case prop encoding time   : 0.000
% 33.47/33.70  #    Success case prop solver time     : 0.000
% 33.47/33.70  # Current number of processed clauses  : 2111
% 33.47/33.70  #    Positive orientable unit clauses  : 57
% 33.47/33.70  #    Positive unorientable unit clauses: 1
% 33.47/33.70  #    Negative unit clauses             : 6
% 33.47/33.70  #    Non-unit-clauses                  : 2047
% 33.47/33.70  # Current number of unprocessed clauses: 1517917
% 33.47/33.70  # ...number of literals in the above   : 11245595
% 33.47/33.70  # Current number of archived formulas  : 0
% 33.47/33.70  # Current number of archived clauses   : 613
% 33.47/33.70  # Clause-clause subsumption calls (NU) : 606721
% 33.47/33.70  # Rec. Clause-clause subsumption calls : 183365
% 33.47/33.70  # Non-unit clause-clause subsumptions  : 5827
% 33.47/33.70  # Unit Clause-clause subsumption calls : 4238
% 33.47/33.70  # Rewrite failures with RHS unbound    : 16
% 33.47/33.70  # BW rewrite match attempts            : 444
% 33.47/33.70  # BW rewrite match successes           : 59
% 33.47/33.70  # Condensation attempts                : 0
% 33.47/33.70  # Condensation successes               : 0
% 33.47/33.70  # Termbank termtop insertions          : 52152151
% 33.54/33.79  
% 33.54/33.79  # -------------------------------------------------
% 33.54/33.79  # User time                : 32.569 s
% 33.54/33.79  # System time              : 0.877 s
% 33.54/33.79  # Total time               : 33.446 s
% 33.54/33.79  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
