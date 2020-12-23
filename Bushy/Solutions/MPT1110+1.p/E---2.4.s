%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : pre_topc__t39_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:43 EDT 2019

% Result     : Theorem 0.66s
% Output     : CNFRefutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 515 expanded)
%              Number of clauses        :   67 ( 228 expanded)
%              Number of leaves         :   18 ( 127 expanded)
%              Depth                    :   23
%              Number of atoms          :  304 (1661 expanded)
%              Number of equality atoms :   34 ( 111 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',d9_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',dt_m1_pre_topc)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',t5_subset)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',dt_k9_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',existence_m1_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',redefinition_k9_subset_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',t2_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',commutativity_k3_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',t3_subset)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',idempotence_k9_subset_1)).

fof(t39_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',t39_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',dt_l1_pre_topc)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',t1_xboole_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',t1_subset)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',t8_boole)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t39_pre_topc.p',dt_k2_struct_0)).

fof(c_0_18,plain,(
    ! [X16,X17,X18,X20,X22] :
      ( ( r1_tarski(k2_struct_0(X17),k2_struct_0(X16))
        | ~ m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk4_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk4_3(X16,X17,X18),u1_pre_topc(X16))
        | ~ r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( X18 = k9_subset_1(u1_struct_0(X17),esk4_3(X16,X17,X18),k2_struct_0(X17))
        | ~ r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r2_hidden(X20,u1_pre_topc(X16))
        | X18 != k9_subset_1(u1_struct_0(X17),X20,k2_struct_0(X17))
        | r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk5_2(X16,X17),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r1_tarski(k2_struct_0(X17),k2_struct_0(X16))
        | m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( ~ r2_hidden(esk5_2(X16,X17),u1_pre_topc(X17))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r2_hidden(X22,u1_pre_topc(X16))
        | esk5_2(X16,X17) != k9_subset_1(u1_struct_0(X17),X22,k2_struct_0(X17))
        | ~ r1_tarski(k2_struct_0(X17),k2_struct_0(X16))
        | m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk6_2(X16,X17),k1_zfmisc_1(u1_struct_0(X16)))
        | r2_hidden(esk5_2(X16,X17),u1_pre_topc(X17))
        | ~ r1_tarski(k2_struct_0(X17),k2_struct_0(X16))
        | m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk6_2(X16,X17),u1_pre_topc(X16))
        | r2_hidden(esk5_2(X16,X17),u1_pre_topc(X17))
        | ~ r1_tarski(k2_struct_0(X17),k2_struct_0(X16))
        | m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) )
      & ( esk5_2(X16,X17) = k9_subset_1(u1_struct_0(X17),esk6_2(X16,X17),k2_struct_0(X17))
        | r2_hidden(esk5_2(X16,X17),u1_pre_topc(X17))
        | ~ r1_tarski(k2_struct_0(X17),k2_struct_0(X16))
        | m1_pre_topc(X17,X16)
        | ~ l1_pre_topc(X17)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_19,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_pre_topc(X30,X29)
      | l1_pre_topc(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_20,plain,(
    ! [X58,X59,X60] :
      ( ~ r2_hidden(X58,X59)
      | ~ m1_subset_1(X59,k1_zfmisc_1(X60))
      | ~ v1_xboole_0(X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_21,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X25))
      | m1_subset_1(k9_subset_1(X25,X26,X27),k1_zfmisc_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_22,plain,(
    ! [X51,X52] :
      ( ~ m1_subset_1(X51,X52)
      | v1_xboole_0(X52)
      | r2_hidden(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_23,plain,(
    ! [X36] : m1_subset_1(esk10_1(X36),X36) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_24,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X42))
      | k9_subset_1(X42,X43,X44) = k3_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_25,plain,(
    ! [X50] : k3_xboole_0(X50,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_26,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_27,plain,(
    ! [X53,X54] :
      ( ( ~ m1_subset_1(X53,k1_zfmisc_1(X54))
        | r1_tarski(X53,X54) )
      & ( ~ r1_tarski(X53,X54)
        | m1_subset_1(X53,k1_zfmisc_1(X54)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_28,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk10_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X39))
      | k9_subset_1(X39,X40,X40) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

cnf(c_0_35,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
               => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_pre_topc])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k9_subset_1(X1,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk10_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_35])).

cnf(c_0_45,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k2_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).

fof(c_0_48,plain,(
    ! [X15] :
      ( ~ l1_struct_0(X15)
      | k2_struct_0(X15) = u1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_49,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k9_subset_1(X1,X2,X3))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( k9_subset_1(X1,X2,X2) = X2 ),
    inference(spm,[status(thm)],[c_0_43,c_0_33])).

cnf(c_0_52,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_struct_0(X1)))
    | r2_hidden(k2_struct_0(X2),k1_zfmisc_1(k2_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_33])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k2_struct_0(esk1_0)))
    | r2_hidden(k2_struct_0(esk2_0),k1_zfmisc_1(k2_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_61,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_hidden(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_55])])).

fof(c_0_64,plain,(
    ! [X47,X48,X49] :
      ( ~ r1_tarski(X47,X48)
      | ~ r1_tarski(X48,X49)
      | r1_tarski(X47,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_65,plain,(
    ! [X45,X46] :
      ( ~ r2_hidden(X45,X46)
      | m1_subset_1(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0)
    | r2_hidden(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_54]),c_0_55])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0)
    | r2_hidden(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_61]),c_0_67])])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0)
    | m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

fof(c_0_74,plain,(
    ! [X64,X65] :
      ( ~ v1_xboole_0(X64)
      | X64 = X65
      | ~ v1_xboole_0(X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_75,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0)
    | r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0)
    | r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_79,negated_conjecture,
    ( X1 = k1_zfmisc_1(u1_struct_0(esk1_0))
    | r2_hidden(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_63])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0)
    | r1_tarski(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_82,negated_conjecture,
    ( X1 = k1_zfmisc_1(u1_struct_0(esk1_0))
    | r2_hidden(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_61]),c_0_67])])).

cnf(c_0_83,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_80]),c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( k1_zfmisc_1(u1_struct_0(esk1_0)) = k1_xboole_0
    | r2_hidden(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

fof(c_0_85,plain,(
    ! [X24] :
      ( ~ l1_struct_0(X24)
      | m1_subset_1(k2_struct_0(X24),k1_zfmisc_1(u1_struct_0(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_86,negated_conjecture,
    ( k1_zfmisc_1(u1_struct_0(esk1_0)) = k1_xboole_0
    | m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_84])).

cnf(c_0_87,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( k1_zfmisc_1(u1_struct_0(esk1_0)) = k1_xboole_0
    | r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_86])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,u1_struct_0(X2))
    | ~ r1_tarski(X1,k2_struct_0(X2))
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( k1_zfmisc_1(u1_struct_0(esk1_0)) = k1_xboole_0
    | r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_69])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,k2_struct_0(X2))
    | ~ r1_tarski(X1,k2_struct_0(X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_39])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_69])).

cnf(c_0_93,negated_conjecture,
    ( k1_zfmisc_1(u1_struct_0(esk1_0)) = k1_xboole_0
    | r1_tarski(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_78])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k2_struct_0(X2))
    | ~ r1_tarski(X1,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_61]),c_0_29])).

cnf(c_0_95,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( k1_zfmisc_1(u1_struct_0(esk1_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_93]),c_0_81])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,k2_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_94,c_0_69])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(X1,k1_xboole_0)
    | ~ l1_struct_0(esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk3_0,k2_struct_0(X1))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_78])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_57]),c_0_55])])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_struct_0(X1)))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_99])).

cnf(c_0_102,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_96])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_54]),c_0_55])]),c_0_102]),
    [proof]).
%------------------------------------------------------------------------------
