%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:20 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 140 expanded)
%              Number of clauses        :   41 (  62 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  292 ( 663 expanded)
%              Number of equality atoms :   45 ( 101 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

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

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ~ r1_tarski(X5,X6)
      | k3_xboole_0(X5,X6) = X5 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_14,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X12))
      | k9_subset_1(X12,X13,X14) = k3_xboole_0(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_16,plain,(
    ! [X22,X23,X24,X26,X28] :
      ( ( r1_tarski(k2_struct_0(X23),k2_struct_0(X22))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk1_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X24,u1_pre_topc(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(esk1_3(X22,X23,X24),u1_pre_topc(X22))
        | ~ r2_hidden(X24,u1_pre_topc(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( X24 = k9_subset_1(u1_struct_0(X23),esk1_3(X22,X23,X24),k2_struct_0(X23))
        | ~ r2_hidden(X24,u1_pre_topc(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X26,u1_pre_topc(X22))
        | X24 != k9_subset_1(u1_struct_0(X23),X26,k2_struct_0(X23))
        | r2_hidden(X24,u1_pre_topc(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk2_2(X22,X23),k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r1_tarski(k2_struct_0(X23),k2_struct_0(X22))
        | m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( ~ r2_hidden(esk2_2(X22,X23),u1_pre_topc(X23))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X28,u1_pre_topc(X22))
        | esk2_2(X22,X23) != k9_subset_1(u1_struct_0(X23),X28,k2_struct_0(X23))
        | ~ r1_tarski(k2_struct_0(X23),k2_struct_0(X22))
        | m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk3_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))
        | r2_hidden(esk2_2(X22,X23),u1_pre_topc(X23))
        | ~ r1_tarski(k2_struct_0(X23),k2_struct_0(X22))
        | m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(esk3_2(X22,X23),u1_pre_topc(X22))
        | r2_hidden(esk2_2(X22,X23),u1_pre_topc(X23))
        | ~ r1_tarski(k2_struct_0(X23),k2_struct_0(X22))
        | m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( esk2_2(X22,X23) = k9_subset_1(u1_struct_0(X23),esk3_2(X22,X23),k2_struct_0(X23))
        | r2_hidden(esk2_2(X22,X23),u1_pre_topc(X23))
        | ~ r1_tarski(k2_struct_0(X23),k2_struct_0(X22))
        | m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_17,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_pre_topc(X33,X32)
      | l1_pre_topc(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_18,plain,(
    ! [X19,X20,X21] :
      ( ( X21 != k1_pre_topc(X19,X20)
        | k2_struct_0(X21) = X20
        | ~ v1_pre_topc(X21)
        | ~ m1_pre_topc(X21,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( k2_struct_0(X21) != X20
        | X21 = k1_pre_topc(X19,X20)
        | ~ v1_pre_topc(X21)
        | ~ m1_pre_topc(X21,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_19,plain,(
    ! [X30,X31] :
      ( ( v1_pre_topc(k1_pre_topc(X30,X31))
        | ~ l1_pre_topc(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))) )
      & ( m1_pre_topc(k1_pre_topc(X30,X31),X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X7))
      | k9_subset_1(X7,X8,X9) = k9_subset_1(X7,X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_31,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_33,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k9_subset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_35,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_struct_0(X2))
    | ~ m1_pre_topc(k1_pre_topc(X3,X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k9_subset_1(X1,X2,X3) = X3
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

fof(c_0_40,plain,(
    ! [X11] : m1_subset_1(k2_subset_1(X11),k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_41,plain,(
    ! [X10] : k2_subset_1(X10) = X10 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_42,plain,(
    ! [X34,X35,X36,X38] :
      ( ( m1_subset_1(esk4_3(X34,X35,X36),k1_zfmisc_1(u1_struct_0(X34)))
        | ~ v4_pre_topc(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_pre_topc(X35,X34)
        | ~ l1_pre_topc(X34) )
      & ( v4_pre_topc(esk4_3(X34,X35,X36),X34)
        | ~ v4_pre_topc(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_pre_topc(X35,X34)
        | ~ l1_pre_topc(X34) )
      & ( k9_subset_1(u1_struct_0(X35),esk4_3(X34,X35,X36),k2_struct_0(X35)) = X36
        | ~ v4_pre_topc(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_pre_topc(X35,X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ v4_pre_topc(X38,X34)
        | k9_subset_1(u1_struct_0(X35),X38,k2_struct_0(X35)) != X36
        | v4_pre_topc(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_pre_topc(X35,X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).

cnf(c_0_43,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( v4_pre_topc(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3)) != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_50,negated_conjecture,(
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

cnf(c_0_51,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)
    | ~ v4_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(X1),X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_39])).

fof(c_0_53,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & m1_pre_topc(esk7_0,esk5_0)
    & v4_pre_topc(esk6_0,esk5_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & esk8_0 = esk6_0
    & ~ v4_pre_topc(esk8_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_50])])])).

cnf(c_0_54,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_33])).

cnf(c_0_55,plain,
    ( k9_subset_1(X1,k2_struct_0(X2),X3) = X3
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk8_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( ~ v4_pre_topc(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_24])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65]),c_0_66])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.43  #
% 0.21/0.43  # Preprocessing time       : 0.029 s
% 0.21/0.43  # Presaturation interreduction done
% 0.21/0.43  
% 0.21/0.43  # Proof found!
% 0.21/0.43  # SZS status Theorem
% 0.21/0.43  # SZS output start CNFRefutation
% 0.21/0.43  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.43  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.43  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.21/0.43  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.21/0.43  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.43  fof(d10_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((v1_pre_topc(X3)&m1_pre_topc(X3,X1))=>(X3=k1_pre_topc(X1,X2)<=>k2_struct_0(X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 0.21/0.43  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.21/0.43  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.21/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.43  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.21/0.43  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.21/0.43  fof(t43_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X3,X2)<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v4_pre_topc(X4,X1))&k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_pre_topc)).
% 0.21/0.43  fof(t34_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_2)).
% 0.21/0.43  fof(c_0_13, plain, ![X5, X6]:(~r1_tarski(X5,X6)|k3_xboole_0(X5,X6)=X5), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.43  fof(c_0_14, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.21/0.43  fof(c_0_15, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X12))|k9_subset_1(X12,X13,X14)=k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.21/0.43  fof(c_0_16, plain, ![X22, X23, X24, X26, X28]:(((r1_tarski(k2_struct_0(X23),k2_struct_0(X22))|~m1_pre_topc(X23,X22)|~l1_pre_topc(X23)|~l1_pre_topc(X22))&((((m1_subset_1(esk1_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))|~r2_hidden(X24,u1_pre_topc(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~m1_pre_topc(X23,X22)|~l1_pre_topc(X23)|~l1_pre_topc(X22))&(r2_hidden(esk1_3(X22,X23,X24),u1_pre_topc(X22))|~r2_hidden(X24,u1_pre_topc(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~m1_pre_topc(X23,X22)|~l1_pre_topc(X23)|~l1_pre_topc(X22)))&(X24=k9_subset_1(u1_struct_0(X23),esk1_3(X22,X23,X24),k2_struct_0(X23))|~r2_hidden(X24,u1_pre_topc(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~m1_pre_topc(X23,X22)|~l1_pre_topc(X23)|~l1_pre_topc(X22)))&(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X22)))|~r2_hidden(X26,u1_pre_topc(X22))|X24!=k9_subset_1(u1_struct_0(X23),X26,k2_struct_0(X23))|r2_hidden(X24,u1_pre_topc(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~m1_pre_topc(X23,X22)|~l1_pre_topc(X23)|~l1_pre_topc(X22))))&((m1_subset_1(esk2_2(X22,X23),k1_zfmisc_1(u1_struct_0(X23)))|~r1_tarski(k2_struct_0(X23),k2_struct_0(X22))|m1_pre_topc(X23,X22)|~l1_pre_topc(X23)|~l1_pre_topc(X22))&((~r2_hidden(esk2_2(X22,X23),u1_pre_topc(X23))|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X22)))|~r2_hidden(X28,u1_pre_topc(X22))|esk2_2(X22,X23)!=k9_subset_1(u1_struct_0(X23),X28,k2_struct_0(X23)))|~r1_tarski(k2_struct_0(X23),k2_struct_0(X22))|m1_pre_topc(X23,X22)|~l1_pre_topc(X23)|~l1_pre_topc(X22))&(((m1_subset_1(esk3_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))|r2_hidden(esk2_2(X22,X23),u1_pre_topc(X23))|~r1_tarski(k2_struct_0(X23),k2_struct_0(X22))|m1_pre_topc(X23,X22)|~l1_pre_topc(X23)|~l1_pre_topc(X22))&(r2_hidden(esk3_2(X22,X23),u1_pre_topc(X22))|r2_hidden(esk2_2(X22,X23),u1_pre_topc(X23))|~r1_tarski(k2_struct_0(X23),k2_struct_0(X22))|m1_pre_topc(X23,X22)|~l1_pre_topc(X23)|~l1_pre_topc(X22)))&(esk2_2(X22,X23)=k9_subset_1(u1_struct_0(X23),esk3_2(X22,X23),k2_struct_0(X23))|r2_hidden(esk2_2(X22,X23),u1_pre_topc(X23))|~r1_tarski(k2_struct_0(X23),k2_struct_0(X22))|m1_pre_topc(X23,X22)|~l1_pre_topc(X23)|~l1_pre_topc(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.21/0.43  fof(c_0_17, plain, ![X32, X33]:(~l1_pre_topc(X32)|(~m1_pre_topc(X33,X32)|l1_pre_topc(X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.43  fof(c_0_18, plain, ![X19, X20, X21]:((X21!=k1_pre_topc(X19,X20)|k2_struct_0(X21)=X20|(~v1_pre_topc(X21)|~m1_pre_topc(X21,X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(k2_struct_0(X21)!=X20|X21=k1_pre_topc(X19,X20)|(~v1_pre_topc(X21)|~m1_pre_topc(X21,X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).
% 0.21/0.43  fof(c_0_19, plain, ![X30, X31]:((v1_pre_topc(k1_pre_topc(X30,X31))|(~l1_pre_topc(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))))&(m1_pre_topc(k1_pre_topc(X30,X31),X30)|(~l1_pre_topc(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.21/0.43  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.43  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.43  cnf(c_0_22, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.43  cnf(c_0_23, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.43  cnf(c_0_24, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.43  cnf(c_0_25, plain, (k2_struct_0(X1)=X3|X1!=k1_pre_topc(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.43  cnf(c_0_26, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.43  cnf(c_0_27, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.43  fof(c_0_28, plain, ![X7, X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(X7))|k9_subset_1(X7,X8,X9)=k9_subset_1(X7,X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.21/0.43  cnf(c_0_29, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.43  cnf(c_0_30, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.21/0.43  cnf(c_0_31, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.43  cnf(c_0_32, plain, (k2_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_26]), c_0_27])).
% 0.21/0.43  cnf(c_0_33, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.43  cnf(c_0_34, plain, (k9_subset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.43  fof(c_0_35, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.43  cnf(c_0_36, plain, (r1_tarski(X1,k2_struct_0(X2))|~m1_pre_topc(k1_pre_topc(X3,X1),X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.43  cnf(c_0_37, plain, (k9_subset_1(X1,X2,X3)=X3|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.43  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.43  cnf(c_0_39, plain, (r1_tarski(X1,k2_struct_0(X2))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_36, c_0_27])).
% 0.21/0.43  fof(c_0_40, plain, ![X11]:m1_subset_1(k2_subset_1(X11),k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.21/0.43  fof(c_0_41, plain, ![X10]:k2_subset_1(X10)=X10, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.21/0.43  fof(c_0_42, plain, ![X34, X35, X36, X38]:((((m1_subset_1(esk4_3(X34,X35,X36),k1_zfmisc_1(u1_struct_0(X34)))|~v4_pre_topc(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~m1_pre_topc(X35,X34)|~l1_pre_topc(X34))&(v4_pre_topc(esk4_3(X34,X35,X36),X34)|~v4_pre_topc(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~m1_pre_topc(X35,X34)|~l1_pre_topc(X34)))&(k9_subset_1(u1_struct_0(X35),esk4_3(X34,X35,X36),k2_struct_0(X35))=X36|~v4_pre_topc(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~m1_pre_topc(X35,X34)|~l1_pre_topc(X34)))&(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X34)))|~v4_pre_topc(X38,X34)|k9_subset_1(u1_struct_0(X35),X38,k2_struct_0(X35))!=X36|v4_pre_topc(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~m1_pre_topc(X35,X34)|~l1_pre_topc(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).
% 0.21/0.43  cnf(c_0_43, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_30, c_0_37])).
% 0.21/0.43  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X2)))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.43  cnf(c_0_45, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.43  cnf(c_0_46, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.43  cnf(c_0_47, plain, (v4_pre_topc(X4,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3))!=X4|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.43  cnf(c_0_48, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.43  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.43  fof(c_0_50, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3)))))))), inference(assume_negation,[status(cth)],[t34_tops_2])).
% 0.21/0.43  cnf(c_0_51, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)|~v4_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_47])).
% 0.21/0.43  cnf(c_0_52, plain, (k1_setfam_1(k2_tarski(k2_struct_0(X1),X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_39])).
% 0.21/0.43  fof(c_0_53, negated_conjecture, (l1_pre_topc(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(m1_pre_topc(esk7_0,esk5_0)&(v4_pre_topc(esk6_0,esk5_0)&(m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))&(esk8_0=esk6_0&~v4_pre_topc(esk8_0,esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_50])])])).
% 0.21/0.43  cnf(c_0_54, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~v4_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_51, c_0_33])).
% 0.21/0.43  cnf(c_0_55, plain, (k9_subset_1(X1,k2_struct_0(X2),X3)=X3|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_52])).
% 0.21/0.43  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.43  cnf(c_0_57, negated_conjecture, (esk8_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.43  cnf(c_0_58, negated_conjecture, (~v4_pre_topc(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.43  cnf(c_0_59, plain, (v4_pre_topc(X1,X2)|~v4_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_24])).
% 0.21/0.43  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.43  cnf(c_0_61, negated_conjecture, (~v4_pre_topc(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_58, c_0_57])).
% 0.21/0.43  cnf(c_0_62, negated_conjecture, (~v4_pre_topc(esk6_0,X1)|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.21/0.43  cnf(c_0_63, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.43  cnf(c_0_64, negated_conjecture, (m1_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.43  cnf(c_0_65, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.43  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.43  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65]), c_0_66])]), ['proof']).
% 0.21/0.43  # SZS output end CNFRefutation
% 0.21/0.43  # Proof object total steps             : 68
% 0.21/0.43  # Proof object clause steps            : 41
% 0.21/0.43  # Proof object formula steps           : 27
% 0.21/0.43  # Proof object conjectures             : 14
% 0.21/0.43  # Proof object clause conjectures      : 11
% 0.21/0.43  # Proof object formula conjectures     : 3
% 0.21/0.43  # Proof object initial clauses used    : 20
% 0.21/0.43  # Proof object initial formulas used   : 13
% 0.21/0.43  # Proof object generating inferences   : 13
% 0.21/0.43  # Proof object simplifying inferences  : 17
% 0.21/0.43  # Training examples: 0 positive, 0 negative
% 0.21/0.43  # Parsed axioms                        : 13
% 0.21/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.43  # Initial clauses                      : 34
% 0.21/0.43  # Removed in clause preprocessing      : 2
% 0.21/0.43  # Initial clauses in saturation        : 32
% 0.21/0.43  # Processed clauses                    : 627
% 0.21/0.43  # ...of these trivial                  : 1
% 0.21/0.43  # ...subsumed                          : 386
% 0.21/0.43  # ...remaining for further processing  : 240
% 0.21/0.43  # Other redundant clauses eliminated   : 4
% 0.21/0.43  # Clauses deleted for lack of memory   : 0
% 0.21/0.43  # Backward-subsumed                    : 11
% 0.21/0.43  # Backward-rewritten                   : 0
% 0.21/0.43  # Generated clauses                    : 1298
% 0.21/0.43  # ...of the previous two non-trivial   : 1240
% 0.21/0.43  # Contextual simplify-reflections      : 29
% 0.21/0.43  # Paramodulations                      : 1294
% 0.21/0.43  # Factorizations                       : 0
% 0.21/0.43  # Equation resolutions                 : 4
% 0.21/0.43  # Propositional unsat checks           : 0
% 0.21/0.43  #    Propositional check models        : 0
% 0.21/0.43  #    Propositional check unsatisfiable : 0
% 0.21/0.43  #    Propositional clauses             : 0
% 0.21/0.43  #    Propositional clauses after purity: 0
% 0.21/0.43  #    Propositional unsat core size     : 0
% 0.21/0.43  #    Propositional preprocessing time  : 0.000
% 0.21/0.43  #    Propositional encoding time       : 0.000
% 0.21/0.43  #    Propositional solver time         : 0.000
% 0.21/0.43  #    Success case prop preproc time    : 0.000
% 0.21/0.43  #    Success case prop encoding time   : 0.000
% 0.21/0.43  #    Success case prop solver time     : 0.000
% 0.21/0.43  # Current number of processed clauses  : 193
% 0.21/0.43  #    Positive orientable unit clauses  : 9
% 0.21/0.43  #    Positive unorientable unit clauses: 0
% 0.21/0.43  #    Negative unit clauses             : 1
% 0.21/0.43  #    Non-unit-clauses                  : 183
% 0.21/0.43  # Current number of unprocessed clauses: 653
% 0.21/0.43  # ...number of literals in the above   : 4492
% 0.21/0.43  # Current number of archived formulas  : 0
% 0.21/0.43  # Current number of archived clauses   : 45
% 0.21/0.43  # Clause-clause subsumption calls (NU) : 22040
% 0.21/0.43  # Rec. Clause-clause subsumption calls : 4224
% 0.21/0.43  # Non-unit clause-clause subsumptions  : 426
% 0.21/0.43  # Unit Clause-clause subsumption calls : 79
% 0.21/0.43  # Rewrite failures with RHS unbound    : 0
% 0.21/0.43  # BW rewrite match attempts            : 2
% 0.21/0.43  # BW rewrite match successes           : 0
% 0.21/0.43  # Condensation attempts                : 0
% 0.21/0.43  # Condensation successes               : 0
% 0.21/0.43  # Termbank termtop insertions          : 34940
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.082 s
% 0.21/0.43  # System time              : 0.007 s
% 0.21/0.43  # Total time               : 0.089 s
% 0.21/0.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
