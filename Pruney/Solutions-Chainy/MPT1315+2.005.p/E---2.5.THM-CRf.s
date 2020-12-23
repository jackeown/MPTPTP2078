%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:19 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 260 expanded)
%              Number of clauses        :   33 (  99 expanded)
%              Number of leaves         :   10 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  236 (1252 expanded)
%              Number of equality atoms :   40 ( 183 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & m1_pre_topc(esk7_0,esk5_0)
    & v4_pre_topc(esk6_0,esk5_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & esk8_0 = esk6_0
    & ~ v4_pre_topc(esk8_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_pre_topc(X29,X28)
      | l1_pre_topc(X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_13,plain,(
    ! [X15,X16,X17] :
      ( ( X17 != k1_pre_topc(X15,X16)
        | k2_struct_0(X17) = X16
        | ~ v1_pre_topc(X17)
        | ~ m1_pre_topc(X17,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( k2_struct_0(X17) != X16
        | X17 = k1_pre_topc(X15,X16)
        | ~ v1_pre_topc(X17)
        | ~ m1_pre_topc(X17,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_14,plain,(
    ! [X26,X27] :
      ( ( v1_pre_topc(k1_pre_topc(X26,X27))
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) )
      & ( m1_pre_topc(k1_pre_topc(X26,X27),X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_15,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X12))
      | k9_subset_1(X12,X13,X14) = k3_xboole_0(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X22,X24] :
      ( ( r1_tarski(k2_struct_0(X19),k2_struct_0(X18))
        | ~ m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk1_3(X18,X19,X20),k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r2_hidden(X20,u1_pre_topc(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk1_3(X18,X19,X20),u1_pre_topc(X18))
        | ~ r2_hidden(X20,u1_pre_topc(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( X20 = k9_subset_1(u1_struct_0(X19),esk1_3(X18,X19,X20),k2_struct_0(X19))
        | ~ r2_hidden(X20,u1_pre_topc(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r2_hidden(X22,u1_pre_topc(X18))
        | X20 != k9_subset_1(u1_struct_0(X19),X22,k2_struct_0(X19))
        | r2_hidden(X20,u1_pre_topc(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk2_2(X18,X19),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r1_tarski(k2_struct_0(X19),k2_struct_0(X18))
        | m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( ~ r2_hidden(esk2_2(X18,X19),u1_pre_topc(X19))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r2_hidden(X24,u1_pre_topc(X18))
        | esk2_2(X18,X19) != k9_subset_1(u1_struct_0(X19),X24,k2_struct_0(X19))
        | ~ r1_tarski(k2_struct_0(X19),k2_struct_0(X18))
        | m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk3_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))
        | r2_hidden(esk2_2(X18,X19),u1_pre_topc(X19))
        | ~ r1_tarski(k2_struct_0(X19),k2_struct_0(X18))
        | m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( r2_hidden(esk3_2(X18,X19),u1_pre_topc(X18))
        | r2_hidden(esk2_2(X18,X19),u1_pre_topc(X19))
        | ~ r1_tarski(k2_struct_0(X19),k2_struct_0(X18))
        | m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) )
      & ( esk2_2(X18,X19) = k9_subset_1(u1_struct_0(X19),esk3_2(X18,X19),k2_struct_0(X19))
        | r2_hidden(esk2_2(X18,X19),u1_pre_topc(X19))
        | ~ r1_tarski(k2_struct_0(X19),k2_struct_0(X18))
        | m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X19)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( esk8_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_30,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23]),c_0_24])).

fof(c_0_31,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_32,plain,(
    ! [X30,X31,X32,X34] :
      ( ( m1_subset_1(esk4_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X30)))
        | ~ v4_pre_topc(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_pre_topc(X31,X30)
        | ~ l1_pre_topc(X30) )
      & ( v4_pre_topc(esk4_3(X30,X31,X32),X30)
        | ~ v4_pre_topc(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_pre_topc(X31,X30)
        | ~ l1_pre_topc(X30) )
      & ( k9_subset_1(u1_struct_0(X31),esk4_3(X30,X31,X32),k2_struct_0(X31)) = X32
        | ~ v4_pre_topc(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_pre_topc(X31,X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ v4_pre_topc(X34,X30)
        | k9_subset_1(u1_struct_0(X31),X34,k2_struct_0(X31)) != X32
        | v4_pre_topc(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_pre_topc(X31,X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).

fof(c_0_33,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | k9_subset_1(X9,X10,X11) = k9_subset_1(X9,X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(X1,esk6_0) = k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_35,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k3_xboole_0(X7,X8) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk7_0,esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_28]),c_0_29])])).

cnf(c_0_38,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk7_0,esk6_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_29])])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( v4_pre_topc(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3)) != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),X1,esk6_0) = k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_28]),c_0_34])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk6_0,k2_struct_0(esk7_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_29])]),c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(esk6_0,X1) = k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( ~ v4_pre_topc(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)
    | ~ v4_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),esk6_0,X1) = k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),k2_struct_0(esk7_0),esk6_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_49]),c_0_28])]),c_0_50])).

cnf(c_0_52,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_26]),c_0_52]),c_0_20]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:43:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.12/0.37  # and selection function SelectComplexG.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.029 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t34_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_2)).
% 0.12/0.37  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.12/0.37  fof(d10_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((v1_pre_topc(X3)&m1_pre_topc(X3,X1))=>(X3=k1_pre_topc(X1,X2)<=>k2_struct_0(X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 0.12/0.37  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.12/0.37  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.12/0.37  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.12/0.37  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.12/0.37  fof(t43_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X3,X2)<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v4_pre_topc(X4,X1))&k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_pre_topc)).
% 0.12/0.37  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.12/0.37  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.37  fof(c_0_10, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3)))))))), inference(assume_negation,[status(cth)],[t34_tops_2])).
% 0.12/0.37  fof(c_0_11, negated_conjecture, (l1_pre_topc(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(m1_pre_topc(esk7_0,esk5_0)&(v4_pre_topc(esk6_0,esk5_0)&(m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))&(esk8_0=esk6_0&~v4_pre_topc(esk8_0,esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X28, X29]:(~l1_pre_topc(X28)|(~m1_pre_topc(X29,X28)|l1_pre_topc(X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.12/0.37  fof(c_0_13, plain, ![X15, X16, X17]:((X17!=k1_pre_topc(X15,X16)|k2_struct_0(X17)=X16|(~v1_pre_topc(X17)|~m1_pre_topc(X17,X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(k2_struct_0(X17)!=X16|X17=k1_pre_topc(X15,X16)|(~v1_pre_topc(X17)|~m1_pre_topc(X17,X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).
% 0.12/0.37  fof(c_0_14, plain, ![X26, X27]:((v1_pre_topc(k1_pre_topc(X26,X27))|(~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))))&(m1_pre_topc(k1_pre_topc(X26,X27),X26)|(~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.12/0.37  fof(c_0_15, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X12))|k9_subset_1(X12,X13,X14)=k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.12/0.37  fof(c_0_16, plain, ![X18, X19, X20, X22, X24]:(((r1_tarski(k2_struct_0(X19),k2_struct_0(X18))|~m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18))&((((m1_subset_1(esk1_3(X18,X19,X20),k1_zfmisc_1(u1_struct_0(X18)))|~r2_hidden(X20,u1_pre_topc(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18))&(r2_hidden(esk1_3(X18,X19,X20),u1_pre_topc(X18))|~r2_hidden(X20,u1_pre_topc(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18)))&(X20=k9_subset_1(u1_struct_0(X19),esk1_3(X18,X19,X20),k2_struct_0(X19))|~r2_hidden(X20,u1_pre_topc(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18)))&(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X18)))|~r2_hidden(X22,u1_pre_topc(X18))|X20!=k9_subset_1(u1_struct_0(X19),X22,k2_struct_0(X19))|r2_hidden(X20,u1_pre_topc(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18))))&((m1_subset_1(esk2_2(X18,X19),k1_zfmisc_1(u1_struct_0(X19)))|~r1_tarski(k2_struct_0(X19),k2_struct_0(X18))|m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18))&((~r2_hidden(esk2_2(X18,X19),u1_pre_topc(X19))|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X18)))|~r2_hidden(X24,u1_pre_topc(X18))|esk2_2(X18,X19)!=k9_subset_1(u1_struct_0(X19),X24,k2_struct_0(X19)))|~r1_tarski(k2_struct_0(X19),k2_struct_0(X18))|m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18))&(((m1_subset_1(esk3_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))|r2_hidden(esk2_2(X18,X19),u1_pre_topc(X19))|~r1_tarski(k2_struct_0(X19),k2_struct_0(X18))|m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18))&(r2_hidden(esk3_2(X18,X19),u1_pre_topc(X18))|r2_hidden(esk2_2(X18,X19),u1_pre_topc(X19))|~r1_tarski(k2_struct_0(X19),k2_struct_0(X18))|m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18)))&(esk2_2(X18,X19)=k9_subset_1(u1_struct_0(X19),esk3_2(X18,X19),k2_struct_0(X19))|r2_hidden(esk2_2(X18,X19),u1_pre_topc(X19))|~r1_tarski(k2_struct_0(X19),k2_struct_0(X18))|m1_pre_topc(X19,X18)|~l1_pre_topc(X19)|~l1_pre_topc(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (esk8_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_19, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_22, plain, (k2_struct_0(X1)=X3|X1!=k1_pre_topc(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_23, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_24, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_25, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_27, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.12/0.37  cnf(c_0_30, plain, (k2_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]), c_0_23]), c_0_24])).
% 0.12/0.37  fof(c_0_31, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.12/0.37  fof(c_0_32, plain, ![X30, X31, X32, X34]:((((m1_subset_1(esk4_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X30)))|~v4_pre_topc(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~m1_pre_topc(X31,X30)|~l1_pre_topc(X30))&(v4_pre_topc(esk4_3(X30,X31,X32),X30)|~v4_pre_topc(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~m1_pre_topc(X31,X30)|~l1_pre_topc(X30)))&(k9_subset_1(u1_struct_0(X31),esk4_3(X30,X31,X32),k2_struct_0(X31))=X32|~v4_pre_topc(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~m1_pre_topc(X31,X30)|~l1_pre_topc(X30)))&(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X30)))|~v4_pre_topc(X34,X30)|k9_subset_1(u1_struct_0(X31),X34,k2_struct_0(X31))!=X32|v4_pre_topc(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~m1_pre_topc(X31,X30)|~l1_pre_topc(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).
% 0.12/0.37  fof(c_0_33, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X9))|k9_subset_1(X9,X10,X11)=k9_subset_1(X9,X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (k3_xboole_0(X1,esk6_0)=k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  fof(c_0_35, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k3_xboole_0(X7,X8)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.12/0.37  cnf(c_0_36, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_27, c_0_19])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk7_0,esk6_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_28]), c_0_29])])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (k2_struct_0(k1_pre_topc(esk7_0,esk6_0))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_28]), c_0_29])])).
% 0.12/0.37  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_40, plain, (v4_pre_topc(X4,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3))!=X4|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_41, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (k9_subset_1(u1_struct_0(esk7_0),X1,esk6_0)=k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_28]), c_0_34])).
% 0.12/0.37  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (r1_tarski(esk6_0,k2_struct_0(esk7_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_29])]), c_0_38])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (k3_xboole_0(esk6_0,X1)=k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (~v4_pre_topc(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_47, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)|~v4_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_40])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (k9_subset_1(u1_struct_0(esk7_0),esk6_0,X1)=k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_28]), c_0_42])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),k2_struct_0(esk7_0),esk6_0)=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (~v4_pre_topc(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_46, c_0_18])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (~v4_pre_topc(esk6_0,X1)|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_49]), c_0_28])]), c_0_50])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_26]), c_0_52]), c_0_20]), c_0_21])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 54
% 0.12/0.37  # Proof object clause steps            : 33
% 0.12/0.37  # Proof object formula steps           : 21
% 0.12/0.37  # Proof object conjectures             : 23
% 0.12/0.37  # Proof object clause conjectures      : 20
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 17
% 0.12/0.37  # Proof object initial formulas used   : 10
% 0.12/0.37  # Proof object generating inferences   : 11
% 0.12/0.37  # Proof object simplifying inferences  : 28
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 30
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 30
% 0.12/0.37  # Processed clauses                    : 90
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 2
% 0.12/0.37  # ...remaining for further processing  : 87
% 0.12/0.37  # Other redundant clauses eliminated   : 4
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 62
% 0.12/0.37  # ...of the previous two non-trivial   : 55
% 0.12/0.37  # Contextual simplify-reflections      : 7
% 0.12/0.37  # Paramodulations                      : 58
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 4
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 53
% 0.12/0.37  #    Positive orientable unit clauses  : 25
% 0.12/0.37  #    Positive unorientable unit clauses: 1
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 26
% 0.12/0.37  # Current number of unprocessed clauses: 24
% 0.12/0.37  # ...number of literals in the above   : 113
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 30
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 494
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 37
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.12/0.37  # Unit Clause-clause subsumption calls : 3
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 6
% 0.12/0.37  # BW rewrite match successes           : 4
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4749
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.035 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.038 s
% 0.12/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
