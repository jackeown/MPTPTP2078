%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:19 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 193 expanded)
%              Number of clauses        :   41 (  76 expanded)
%              Number of leaves         :   15 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  215 ( 846 expanded)
%              Number of equality atoms :   52 ( 148 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( X3 = X4
                   => k2_pre_topc(X2,X4) = k9_subset_1(u1_struct_0(X2),k2_pre_topc(X1,X3),k2_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_pre_topc)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(t34_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v4_pre_topc(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                   => ( X4 = X2
                     => v4_pre_topc(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

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

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t43_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( v4_pre_topc(X3,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v4_pre_topc(X4,X1)
                    & k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

fof(c_0_15,plain,(
    ! [X34,X35,X36,X37] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_pre_topc(X35,X34)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
      | X36 != X37
      | k2_pre_topc(X35,X37) = k9_subset_1(u1_struct_0(X35),k2_pre_topc(X34,X36),k2_struct_0(X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_pre_topc])])])).

fof(c_0_16,plain,(
    ! [X26,X27,X28] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,X26)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_pre_topc(X3,X1)
               => ( v4_pre_topc(X2,X1)
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                     => ( X4 = X2
                       => v4_pre_topc(X4,X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_tops_2])).

cnf(c_0_18,plain,
    ( k2_pre_topc(X2,X4) = k9_subset_1(u1_struct_0(X2),k2_pre_topc(X1,X3),k2_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != X4 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X40,X41] :
      ( ( ~ v4_pre_topc(X41,X40)
        | k2_pre_topc(X40,X41) = X41
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ l1_pre_topc(X40) )
      & ( ~ v2_pre_topc(X40)
        | k2_pre_topc(X40,X41) != X41
        | v4_pre_topc(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_pre_topc(esk4_0,esk2_0)
    & v4_pre_topc(esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & esk5_0 = esk3_0
    & ~ v4_pre_topc(esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_22,plain,(
    ! [X15,X16,X17] : r1_tarski(k2_xboole_0(k3_xboole_0(X15,X16),k3_xboole_0(X15,X17)),k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

fof(c_0_23,plain,(
    ! [X11,X12,X13] : k3_xboole_0(X11,k2_xboole_0(X12,X13)) = k2_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X13)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

fof(c_0_24,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k3_xboole_0(X9,X10)) = X9 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_25,plain,(
    ! [X14] : k3_xboole_0(X14,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_26,plain,
    ( k9_subset_1(u1_struct_0(X1),k2_pre_topc(X2,X3),k2_struct_0(X1)) = k2_pre_topc(X1,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_19])).

cnf(c_0_27,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_34,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X21))
      | k9_subset_1(X21,X22,X23) = k3_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_35,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X18))
      | k9_subset_1(X18,X19,X20) = k9_subset_1(X18,X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_36,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_pre_topc(X1,X2)
    | ~ v4_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_40,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_41,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk3_0,k2_struct_0(esk4_0)) = k2_pre_topc(esk4_0,esk3_0)
    | ~ v4_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_47,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_48,plain,(
    ! [X38,X39] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | r1_tarski(X39,k2_pre_topc(X38,X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk3_0,k2_struct_0(esk4_0)) = k2_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])])).

fof(c_0_53,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | l1_pre_topc(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk3_0,k2_struct_0(esk4_0)) = k2_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_37])]),c_0_50])).

cnf(c_0_58,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_59,plain,(
    ! [X29,X30,X31,X33] :
      ( ( m1_subset_1(esk1_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v4_pre_topc(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_pre_topc(X30,X29)
        | ~ l1_pre_topc(X29) )
      & ( v4_pre_topc(esk1_3(X29,X30,X31),X29)
        | ~ v4_pre_topc(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_pre_topc(X30,X29)
        | ~ l1_pre_topc(X29) )
      & ( k9_subset_1(u1_struct_0(X30),esk1_3(X29,X30,X31),k2_struct_0(X30)) = X31
        | ~ v4_pre_topc(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_pre_topc(X30,X29)
        | ~ l1_pre_topc(X29) )
      & ( ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v4_pre_topc(X33,X29)
        | k9_subset_1(u1_struct_0(X30),X33,k2_struct_0(X30)) != X31
        | v4_pre_topc(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_pre_topc(X30,X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).

cnf(c_0_60,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k2_pre_topc(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk4_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_45]),c_0_46])])).

cnf(c_0_63,plain,
    ( v4_pre_topc(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3)) != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_37])])).

cnf(c_0_65,negated_conjecture,
    ( ~ v4_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_66,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)
    | ~ v4_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk3_0,k2_struct_0(esk4_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( ~ v4_pre_topc(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_37])).

cnf(c_0_70,negated_conjecture,
    ( ~ v4_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_37])]),c_0_68]),c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_45]),c_0_44]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:08:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t47_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X3=X4=>k2_pre_topc(X2,X4)=k9_subset_1(u1_struct_0(X2),k2_pre_topc(X1,X3),k2_struct_0(X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_pre_topc)).
% 0.13/0.38  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.13/0.38  fof(t34_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_2)).
% 0.13/0.38  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.13/0.38  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.13/0.38  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.13/0.38  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.13/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.13/0.38  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.13/0.38  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.13/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(t43_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X3,X2)<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v4_pre_topc(X4,X1))&k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_pre_topc)).
% 0.13/0.38  fof(c_0_15, plain, ![X34, X35, X36, X37]:(~l1_pre_topc(X34)|(~m1_pre_topc(X35,X34)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|(X36!=X37|k2_pre_topc(X35,X37)=k9_subset_1(u1_struct_0(X35),k2_pre_topc(X34,X36),k2_struct_0(X35))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_pre_topc])])])).
% 0.13/0.38  fof(c_0_16, plain, ![X26, X27, X28]:(~l1_pre_topc(X26)|(~m1_pre_topc(X27,X26)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.13/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3)))))))), inference(assume_negation,[status(cth)],[t34_tops_2])).
% 0.13/0.38  cnf(c_0_18, plain, (k2_pre_topc(X2,X4)=k9_subset_1(u1_struct_0(X2),k2_pre_topc(X1,X3),k2_struct_0(X2))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X3!=X4), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_19, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_20, plain, ![X40, X41]:((~v4_pre_topc(X41,X40)|k2_pre_topc(X40,X41)=X41|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~l1_pre_topc(X40))&(~v2_pre_topc(X40)|k2_pre_topc(X40,X41)!=X41|v4_pre_topc(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~l1_pre_topc(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.13/0.38  fof(c_0_21, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_pre_topc(esk4_0,esk2_0)&(v4_pre_topc(esk3_0,esk2_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(esk5_0=esk3_0&~v4_pre_topc(esk5_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.13/0.38  fof(c_0_22, plain, ![X15, X16, X17]:r1_tarski(k2_xboole_0(k3_xboole_0(X15,X16),k3_xboole_0(X15,X17)),k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.13/0.38  fof(c_0_23, plain, ![X11, X12, X13]:k3_xboole_0(X11,k2_xboole_0(X12,X13))=k2_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X13)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.13/0.38  fof(c_0_24, plain, ![X9, X10]:k2_xboole_0(X9,k3_xboole_0(X9,X10))=X9, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.13/0.38  fof(c_0_25, plain, ![X14]:k3_xboole_0(X14,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.13/0.38  cnf(c_0_26, plain, (k9_subset_1(u1_struct_0(X1),k2_pre_topc(X2,X3),k2_struct_0(X1))=k2_pre_topc(X1,X3)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]), c_0_19])).
% 0.13/0.38  cnf(c_0_27, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (esk5_0=esk3_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_30, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_31, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_32, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_33, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  fof(c_0_34, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(X21))|k9_subset_1(X21,X22,X23)=k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.13/0.38  fof(c_0_35, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(X18))|k9_subset_1(X18,X19,X20)=k9_subset_1(X18,X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.13/0.38  cnf(c_0_36, plain, (k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1))=k2_pre_topc(X1,X2)|~v4_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_19])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_38, plain, (r1_tarski(k3_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  cnf(c_0_39, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.38  fof(c_0_40, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.38  cnf(c_0_41, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_42, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk3_0,k2_struct_0(esk4_0))=k2_pre_topc(esk4_0,esk3_0)|~v4_pre_topc(esk3_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (v4_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  fof(c_0_47, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_48, plain, ![X38, X39]:(~l1_pre_topc(X38)|(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|r1_tarski(X39,k2_pre_topc(X38,X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.13/0.38  cnf(c_0_49, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_51, plain, (k9_subset_1(X1,X2,X3)=k3_xboole_0(X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk3_0,k2_struct_0(esk4_0))=k2_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])])).
% 0.13/0.38  fof(c_0_53, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_pre_topc(X25,X24)|l1_pre_topc(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  cnf(c_0_54, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.38  cnf(c_0_55, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.38  cnf(c_0_56, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk3_0,k2_struct_0(esk4_0))=k2_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_37])]), c_0_50])).
% 0.13/0.38  cnf(c_0_58, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.38  fof(c_0_59, plain, ![X29, X30, X31, X33]:((((m1_subset_1(esk1_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X29)))|~v4_pre_topc(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~m1_pre_topc(X30,X29)|~l1_pre_topc(X29))&(v4_pre_topc(esk1_3(X29,X30,X31),X29)|~v4_pre_topc(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~m1_pre_topc(X30,X29)|~l1_pre_topc(X29)))&(k9_subset_1(u1_struct_0(X30),esk1_3(X29,X30,X31),k2_struct_0(X30))=X31|~v4_pre_topc(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~m1_pre_topc(X30,X29)|~l1_pre_topc(X29)))&(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X29)))|~v4_pre_topc(X33,X29)|k9_subset_1(u1_struct_0(X30),X33,k2_struct_0(X30))!=X31|v4_pre_topc(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~m1_pre_topc(X30,X29)|~l1_pre_topc(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).
% 0.13/0.38  cnf(c_0_60, plain, (k2_pre_topc(X1,X2)=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k2_pre_topc(X1,X2),X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (r1_tarski(k2_pre_topc(esk4_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_45]), c_0_46])])).
% 0.13/0.38  cnf(c_0_63, plain, (v4_pre_topc(X4,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3))!=X4|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (k2_pre_topc(esk4_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_37])])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (~v4_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_66, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)|~v4_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_63])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk3_0,k2_struct_0(esk4_0))=esk3_0), inference(rw,[status(thm)],[c_0_52, c_0_64])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (~v4_pre_topc(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_65, c_0_29])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_37])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (~v4_pre_topc(esk3_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_37])]), c_0_68]), c_0_69])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_45]), c_0_44]), c_0_46])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 72
% 0.13/0.38  # Proof object clause steps            : 41
% 0.13/0.38  # Proof object formula steps           : 31
% 0.13/0.38  # Proof object conjectures             : 21
% 0.13/0.38  # Proof object clause conjectures      : 18
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 20
% 0.13/0.38  # Proof object initial formulas used   : 15
% 0.13/0.38  # Proof object generating inferences   : 15
% 0.13/0.38  # Proof object simplifying inferences  : 26
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 15
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 27
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 27
% 0.13/0.38  # Processed clauses                    : 151
% 0.13/0.38  # ...of these trivial                  : 15
% 0.13/0.38  # ...subsumed                          : 34
% 0.13/0.38  # ...remaining for further processing  : 102
% 0.13/0.38  # Other redundant clauses eliminated   : 4
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 9
% 0.13/0.38  # Generated clauses                    : 379
% 0.13/0.38  # ...of the previous two non-trivial   : 222
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 375
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 4
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 63
% 0.13/0.38  #    Positive orientable unit clauses  : 32
% 0.13/0.38  #    Positive unorientable unit clauses: 2
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 27
% 0.13/0.38  # Current number of unprocessed clauses: 105
% 0.13/0.38  # ...number of literals in the above   : 285
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 35
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 431
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 144
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 32
% 0.13/0.38  # Unit Clause-clause subsumption calls : 28
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 24
% 0.13/0.38  # BW rewrite match successes           : 14
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6387
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.037 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.041 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
