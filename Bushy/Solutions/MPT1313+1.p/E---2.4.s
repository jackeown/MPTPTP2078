%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t32_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:38 EDT 2019

% Result     : Theorem 153.15s
% Output     : CNFRefutation 153.15s
% Verified   : 
% Statistics : Number of formulae       :   92 (4562 expanded)
%              Number of clauses        :   71 (1850 expanded)
%              Number of leaves         :   10 (1049 expanded)
%              Depth                    :   21
%              Number of atoms          :  324 (28302 expanded)
%              Number of equality atoms :   34 (3172 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( v3_pre_topc(X3,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',t32_tops_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',dt_m1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',d9_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',dt_l1_pre_topc)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',d5_pre_topc)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',dt_k2_struct_0)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',commutativity_k9_subset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',t1_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',t2_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t32_tops_2.p',t7_boole)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
               => ( v3_pre_topc(X3,X2)
                <=> ? [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                      & v3_pre_topc(X4,X1)
                      & k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) = X3 ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_tops_2])).

fof(c_0_11,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_pre_topc(X33,X32)
      | l1_pre_topc(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_12,negated_conjecture,(
    ! [X8] :
      ( l1_pre_topc(esk1_0)
      & m1_pre_topc(esk2_0,esk1_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ( ~ v3_pre_topc(esk3_0,esk2_0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ v3_pre_topc(X8,esk1_0)
        | k9_subset_1(u1_struct_0(esk2_0),X8,k2_struct_0(esk2_0)) != esk3_0 )
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | v3_pre_topc(esk3_0,esk2_0) )
      & ( v3_pre_topc(esk4_0,esk1_0)
        | v3_pre_topc(esk3_0,esk2_0) )
      & ( k9_subset_1(u1_struct_0(esk2_0),esk4_0,k2_struct_0(esk2_0)) = esk3_0
        | v3_pre_topc(esk3_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

cnf(c_0_13,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X19,X20,X21,X23,X25] :
      ( ( r1_tarski(k2_struct_0(X20),k2_struct_0(X19))
        | ~ m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk5_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(X21,u1_pre_topc(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk5_3(X19,X20,X21),u1_pre_topc(X19))
        | ~ r2_hidden(X21,u1_pre_topc(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( X21 = k9_subset_1(u1_struct_0(X20),esk5_3(X19,X20,X21),k2_struct_0(X20))
        | ~ r2_hidden(X21,u1_pre_topc(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(X23,u1_pre_topc(X19))
        | X21 != k9_subset_1(u1_struct_0(X20),X23,k2_struct_0(X20))
        | r2_hidden(X21,u1_pre_topc(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk6_2(X19,X20),k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r1_tarski(k2_struct_0(X20),k2_struct_0(X19))
        | m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(esk6_2(X19,X20),u1_pre_topc(X20))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(X25,u1_pre_topc(X19))
        | esk6_2(X19,X20) != k9_subset_1(u1_struct_0(X20),X25,k2_struct_0(X20))
        | ~ r1_tarski(k2_struct_0(X20),k2_struct_0(X19))
        | m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk7_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))
        | r2_hidden(esk6_2(X19,X20),u1_pre_topc(X20))
        | ~ r1_tarski(k2_struct_0(X20),k2_struct_0(X19))
        | m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk7_2(X19,X20),u1_pre_topc(X19))
        | r2_hidden(esk6_2(X19,X20),u1_pre_topc(X20))
        | ~ r1_tarski(k2_struct_0(X20),k2_struct_0(X19))
        | m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( esk6_2(X19,X20) = k9_subset_1(u1_struct_0(X20),esk7_2(X19,X20),k2_struct_0(X20))
        | r2_hidden(esk6_2(X19,X20),u1_pre_topc(X20))
        | ~ r1_tarski(k2_struct_0(X20),k2_struct_0(X19))
        | m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_16,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | l1_struct_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X17,X18] :
      ( ( ~ v3_pre_topc(X18,X17)
        | r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( ~ r2_hidden(X18,u1_pre_topc(X17))
        | v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X27] :
      ( ~ l1_struct_0(X27)
      | m1_subset_1(k2_struct_0(X27),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_23,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_19,c_0_13])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_28,plain,
    ( X1 = k9_subset_1(u1_struct_0(X2),esk5_3(X3,X2,X1),k2_struct_0(X2))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_29,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | k9_subset_1(X14,X15,X16) = k9_subset_1(X14,X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_30,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,X1,X2),u1_pre_topc(esk1_0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk2_0))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),esk4_0,k2_struct_0(esk2_0)) = esk3_0
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,X1,X2),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_14])).

cnf(c_0_37,plain,
    ( k9_subset_1(u1_struct_0(X1),esk5_3(X2,X1,X3),k2_struct_0(X1)) = X3
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_28,c_0_13])).

cnf(c_0_38,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,X1),u1_pre_topc(esk1_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),esk4_0,k2_struct_0(esk2_0)) = esk3_0
    | r2_hidden(esk3_0,u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( k9_subset_1(u1_struct_0(X1),esk5_3(esk1_0,X1,X2),k2_struct_0(X1)) = X2
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_14])).

cnf(c_0_46,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),X1) = k9_subset_1(u1_struct_0(esk2_0),X1,k2_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_0,u1_pre_topc(esk2_0))
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_40]),c_0_35])])).

cnf(c_0_48,plain,
    ( r2_hidden(X3,u1_pre_topc(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | X3 != k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(X1,esk1_0)
    | k9_subset_1(u1_struct_0(esk2_0),X1,k2_struct_0(esk2_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),esk4_0,k2_struct_0(esk2_0)) = esk3_0
    | r2_hidden(esk5_3(esk1_0,esk2_0,esk3_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35])])).

cnf(c_0_52,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),esk4_0,k2_struct_0(esk2_0)) = esk3_0
    | m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_35])])).

cnf(c_0_53,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk5_3(esk1_0,esk2_0,X1)) = X1
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_18]),c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk3_0),u1_pre_topc(esk1_0))
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_47]),c_0_35])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_47]),c_0_35])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk1_0))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_58,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_48,c_0_13])])).

cnf(c_0_59,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),esk4_0,k2_struct_0(esk2_0)) = esk3_0
    | k9_subset_1(u1_struct_0(esk2_0),X1,k2_struct_0(esk2_0)) != esk3_0
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_34])).

cnf(c_0_60,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),esk4_0,k2_struct_0(esk2_0)) = esk3_0
    | v3_pre_topc(esk5_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk5_3(esk1_0,esk2_0,esk3_0)) = esk3_0
    | k9_subset_1(u1_struct_0(esk2_0),esk4_0,k2_struct_0(esk2_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_43]),c_0_35])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | k9_subset_1(u1_struct_0(esk2_0),X1,k2_struct_0(esk2_0)) != esk3_0
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(esk5_3(esk1_0,esk2_0,esk3_0),esk1_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_54]),c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk5_3(esk1_0,esk2_0,esk3_0)) = esk3_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_47]),c_0_35])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk4_0,u1_pre_topc(esk1_0))
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_40])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(esk1_0))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_14])).

cnf(c_0_67,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),esk4_0,k2_struct_0(esk2_0)) = esk3_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_46]),c_0_52]),c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_46]),c_0_55]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk4_0,u1_pre_topc(esk1_0))
    | r2_hidden(esk3_0,u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_65]),c_0_35])])).

fof(c_0_70,plain,(
    ! [X48,X49] :
      ( ~ r2_hidden(X48,X49)
      | m1_subset_1(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_71,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_24])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk3_0,u1_pre_topc(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_35]),c_0_68]),c_0_18])]),c_0_69])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_35])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk3_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_72]),c_0_35])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_72]),c_0_35])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk3_0,u1_pre_topc(esk2_0))
    | m1_subset_1(esk4_0,u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),X1,k2_struct_0(esk2_0)) != esk3_0
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_74])])).

cnf(c_0_79,negated_conjecture,
    ( v3_pre_topc(esk5_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_75]),c_0_76])])).

fof(c_0_80,plain,(
    ! [X51,X52] :
      ( ~ m1_subset_1(X51,X52)
      | v1_xboole_0(X52)
      | r2_hidden(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_81,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk5_3(esk1_0,esk2_0,esk3_0)) = esk3_0
    | m1_subset_1(esk4_0,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_77]),c_0_35])])).

cnf(c_0_82,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk5_3(esk1_0,esk2_0,esk3_0)) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_46]),c_0_76])])).

fof(c_0_83,plain,(
    ! [X62,X63] :
      ( ~ r2_hidden(X62,X63)
      | ~ v1_xboole_0(X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_84,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk1_0))
    | r2_hidden(esk4_0,u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk4_0,u1_pre_topc(esk1_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk4_0,u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_75])).

cnf(c_0_90,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_89]),c_0_68])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_90]),c_0_67]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
