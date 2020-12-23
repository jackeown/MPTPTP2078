%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t26_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:37 EDT 2019

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 103 expanded)
%              Number of clauses        :   33 (  42 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  273 ( 455 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t26_tops_2.p',t4_subset)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t26_tops_2.p',dt_k9_subset_1)).

fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t26_tops_2.p',d1_tops_2)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t26_tops_2.p',redefinition_k9_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t26_tops_2.p',d3_tarski)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t26_tops_2.p',commutativity_k3_xboole_0)).

fof(t26_tops_2,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
           => v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t26_tops_2.p',t26_tops_2)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t26_tops_2.p',d5_pre_topc)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t26_tops_2.p',dt_k5_setfam_1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t26_tops_2.p',d1_pre_topc)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t26_tops_2.p',idempotence_k3_xboole_0)).

fof(c_0_11,plain,(
    ! [X59,X60,X61] :
      ( ~ r2_hidden(X59,X60)
      | ~ m1_subset_1(X60,k1_zfmisc_1(X61))
      | m1_subset_1(X59,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_12,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X34))
      | m1_subset_1(k9_subset_1(X34,X35,X36),k1_zfmisc_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_13,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v1_tops_2(X21,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(X22,X21)
        | v3_pre_topc(X22,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk6_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))
        | v1_tops_2(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk6_2(X20,X21),X21)
        | v1_tops_2(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ l1_pre_topc(X20) )
      & ( ~ v3_pre_topc(esk6_2(X20,X21),X20)
        | v1_tops_2(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(X49))
      | k9_subset_1(X49,X50,X51) = k3_xboole_0(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_17,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( ~ r1_tarski(X24,X25)
        | ~ r2_hidden(X26,X24)
        | r2_hidden(X26,X25) )
      & ( r2_hidden(esk7_2(X27,X28),X27)
        | r1_tarski(X27,X28) )
      & ( ~ r2_hidden(esk7_2(X27,X28),X28)
        | r1_tarski(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k9_subset_1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v1_tops_2(X2,X1)
             => v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_tops_2])).

fof(c_0_23,plain,(
    ! [X30,X31] :
      ( ( ~ v3_pre_topc(X31,X30)
        | r2_hidden(X31,u1_pre_topc(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( ~ r2_hidden(X31,u1_pre_topc(X30))
        | v3_pre_topc(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_24,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_25,plain,
    ( r2_hidden(esk7_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & v1_tops_2(esk2_0,esk1_0)
    & ~ v3_pre_topc(k5_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | v3_pre_topc(esk7_2(X1,X2),X3)
    | ~ v1_tops_2(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(X32)))
      | m1_subset_1(k5_setfam_1(X32,X33),k1_zfmisc_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk7_2(X1,X2),u1_pre_topc(X3))
    | ~ v1_tops_2(X1,X3)
    | ~ m1_subset_1(esk7_2(X1,X2),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | m1_subset_1(esk7_2(k3_xboole_0(X1,X2),X3),X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_25])).

cnf(c_0_39,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(esk1_0),esk2_0),u1_pre_topc(esk1_0))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_41,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_43,plain,(
    ! [X13,X14,X15,X16] :
      ( ( r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r1_tarski(X14,u1_pre_topc(X13))
        | r2_hidden(k5_setfam_1(u1_struct_0(X13),X14),u1_pre_topc(X13))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(X15,u1_pre_topc(X13))
        | ~ r2_hidden(X16,u1_pre_topc(X13))
        | r2_hidden(k9_subset_1(u1_struct_0(X13),X15,X16),u1_pre_topc(X13))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk4_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | m1_subset_1(esk3_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk5_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | m1_subset_1(esk3_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk4_1(X13),u1_pre_topc(X13))
        | m1_subset_1(esk3_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk5_1(X13),u1_pre_topc(X13))
        | m1_subset_1(esk3_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X13),esk4_1(X13),esk5_1(X13)),u1_pre_topc(X13))
        | m1_subset_1(esk3_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk4_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | r1_tarski(esk3_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk5_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | r1_tarski(esk3_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk4_1(X13),u1_pre_topc(X13))
        | r1_tarski(esk3_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk5_1(X13),u1_pre_topc(X13))
        | r1_tarski(esk3_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X13),esk4_1(X13),esk5_1(X13)),u1_pre_topc(X13))
        | r1_tarski(esk3_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk4_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk3_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk5_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk3_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk4_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk3_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk5_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk3_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X13),esk4_1(X13),esk5_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk3_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk7_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | r2_hidden(esk7_2(k3_xboole_0(X1,X2),X3),u1_pre_topc(X4))
    | ~ v1_tops_2(k3_xboole_0(X1,X2),X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
    | ~ l1_pre_topc(X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

fof(c_0_46,plain,(
    ! [X43] : k3_xboole_0(X43,X43) = X43 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(esk1_0),esk2_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_48,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),u1_pre_topc(X3))
    | ~ v1_tops_2(k3_xboole_0(X1,X2),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_42]),c_0_35]),c_0_49])])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( v1_tops_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_42]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
