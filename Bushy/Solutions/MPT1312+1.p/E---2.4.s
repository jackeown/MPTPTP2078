%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t31_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:38 EDT 2019

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  146 (1042 expanded)
%              Number of clauses        :  101 ( 492 expanded)
%              Number of leaves         :   22 ( 260 expanded)
%              Depth                    :   19
%              Number of atoms          :  388 (2701 expanded)
%              Number of equality atoms :   35 ( 232 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t5_subset)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',dt_k9_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',existence_m1_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t3_subset)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t79_zfmisc_1)).

fof(t31_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
             => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t31_tops_2)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',idempotence_k9_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t4_subset)).

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
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',d9_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',dt_m1_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',dt_l1_pre_topc)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',dt_k2_struct_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',redefinition_k9_subset_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t2_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',commutativity_k3_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t7_boole)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t1_xboole_1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',antisymmetry_r2_hidden)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t6_boole)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t31_tops_2.p',t1_subset)).

fof(c_0_22,plain,(
    ! [X60,X61,X62] :
      ( ~ r2_hidden(X60,X61)
      | ~ m1_subset_1(X61,k1_zfmisc_1(X62))
      | ~ v1_xboole_0(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_23,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X26))
      | m1_subset_1(k9_subset_1(X26,X27,X28),k1_zfmisc_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_24,plain,(
    ! [X53,X54] :
      ( ~ m1_subset_1(X53,X54)
      | v1_xboole_0(X54)
      | r2_hidden(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_25,plain,(
    ! [X37] : m1_subset_1(esk10_1(X37),X37) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_26,plain,(
    ! [X55,X56] :
      ( ( ~ m1_subset_1(X55,k1_zfmisc_1(X56))
        | r1_tarski(X55,X56) )
      & ( ~ r1_tarski(X55,X56)
        | m1_subset_1(X55,k1_zfmisc_1(X56)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_27,plain,(
    ! [X64,X65] :
      ( ~ r1_tarski(X64,X65)
      | r1_tarski(k1_zfmisc_1(X64),k1_zfmisc_1(X65)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
               => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_tops_2])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk10_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | k9_subset_1(X40,X41,X41) = X41 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X57,X58,X59] :
      ( ~ r2_hidden(X57,X58)
      | ~ m1_subset_1(X58,k1_zfmisc_1(X59))
      | m1_subset_1(X57,X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

fof(c_0_38,plain,(
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

fof(c_0_39,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | l1_pre_topc(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k9_subset_1(X1,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk10_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( m1_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_49,plain,(
    ! [X15] :
      ( ~ l1_struct_0(X15)
      | k2_struct_0(X15) = u1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_50,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_51,plain,
    ( v1_xboole_0(k9_subset_1(X1,X2,X3))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( k9_subset_1(X1,X2,X2) = X2 ),
    inference(spm,[status(thm)],[c_0_42,c_0_32])).

cnf(c_0_53,plain,
    ( m1_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_46])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_59,plain,(
    ! [X24] :
      ( ~ l1_struct_0(X24)
      | m1_subset_1(k2_struct_0(X24),k1_zfmisc_1(u1_struct_0(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_60,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_54]),c_0_55])).

cnf(c_0_63,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(k2_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_56])).

cnf(c_0_64,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_53])).

fof(c_0_67,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(X44))
      | k9_subset_1(X44,X45,X46) = k3_xboole_0(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_68,plain,(
    ! [X52] : k3_xboole_0(X52,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_69,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,esk3_0)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(k2_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_48])).

cnf(c_0_72,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk3_0))
    | ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_46])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | r2_hidden(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_46])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k9_subset_1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_30])).

cnf(c_0_76,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0(X1)))
    | ~ r2_hidden(X2,esk3_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_64]),c_0_58])).

cnf(c_0_81,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_82,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_53])).

cnf(c_0_83,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk3_0))
    | r2_hidden(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_85,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_xboole_0(X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,esk3_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_64])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_hidden(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_90,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk3_0))
    | m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_85])).

fof(c_0_93,plain,(
    ! [X66,X67] :
      ( ~ r2_hidden(X66,X67)
      | ~ v1_xboole_0(X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_81])])).

cnf(c_0_95,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_struct_0(X1)))
    | r2_hidden(k2_struct_0(X2),k1_zfmisc_1(k2_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_63])).

fof(c_0_96,plain,(
    ! [X49,X50,X51] :
      ( ~ r1_tarski(X49,X50)
      | ~ r1_tarski(X50,X51)
      | r1_tarski(X49,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_97,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_76])).

cnf(c_0_98,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk3_0))
    | m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_53])).

cnf(c_0_99,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_64])).

fof(c_0_100,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | ~ r2_hidden(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_101,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_32])).

cnf(c_0_102,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_32])).

fof(c_0_103,plain,(
    ! [X63] :
      ( ~ v1_xboole_0(X63)
      | X63 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_104,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_105,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_hidden(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_41])).

cnf(c_0_106,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k2_struct_0(esk1_0)))
    | r2_hidden(k2_struct_0(esk2_0),k1_zfmisc_1(k2_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_89]),c_0_81])])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_108,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_85])).

cnf(c_0_109,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk3_0))
    | m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_110,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_111,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_112,plain,
    ( v1_xboole_0(k1_xboole_0)
    | m1_subset_1(esk10_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_41])).

cnf(c_0_113,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_41])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_115,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_116,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_hidden(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_64]),c_0_81])])).

cnf(c_0_117,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_44])).

cnf(c_0_118,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_32])).

cnf(c_0_119,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_89]),c_0_81])]),c_0_110])).

cnf(c_0_120,plain,
    ( v1_xboole_0(X1)
    | ~ r2_hidden(X1,esk10_1(X1)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_41])).

cnf(c_0_121,plain,
    ( v1_xboole_0(k1_xboole_0)
    | r2_hidden(esk10_1(k1_xboole_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_112]),c_0_113])).

cnf(c_0_122,negated_conjecture,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))) = k1_xboole_0
    | r2_hidden(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_114,c_0_74])).

fof(c_0_123,plain,(
    ! [X47,X48] :
      ( ~ r2_hidden(X47,X48)
      | m1_subset_1(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_124,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_hidden(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_125,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_89]),c_0_81])])).

cnf(c_0_126,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_127,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_118])).

cnf(c_0_128,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_119])).

cnf(c_0_129,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_113])).

cnf(c_0_130,negated_conjecture,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))) = k1_xboole_0
    | m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_122])).

cnf(c_0_131,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_132,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_hidden(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_64]),c_0_125])])).

cnf(c_0_133,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_44])).

cnf(c_0_134,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_129])])).

cnf(c_0_135,negated_conjecture,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))) = k1_xboole_0
    | m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_53])).

cnf(c_0_136,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_137,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_133])).

cnf(c_0_138,negated_conjecture,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_134])).

cnf(c_0_139,negated_conjecture,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))) = k1_xboole_0
    | v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_110])).

cnf(c_0_140,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_141,negated_conjecture,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_139])).

cnf(c_0_142,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_140])).

cnf(c_0_143,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_141]),c_0_142])).

cnf(c_0_144,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_128])).

cnf(c_0_145,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_143]),c_0_144])]),
    [proof]).
%------------------------------------------------------------------------------
