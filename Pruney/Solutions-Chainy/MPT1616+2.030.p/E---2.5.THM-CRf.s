%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:00 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 108 expanded)
%              Number of clauses        :   33 (  46 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  234 ( 566 expanded)
%              Number of equality atoms :   21 (  48 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(t60_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(c_0_12,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ( ~ m1_setfam_1(X13,X12)
        | r1_tarski(X12,k3_tarski(X13)) )
      & ( ~ r1_tarski(X12,k3_tarski(X13))
        | m1_setfam_1(X13,X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_14,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | ~ v1_xboole_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | r1_tarski(X4,k3_tarski(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k3_tarski(X2)))
    | ~ m1_setfam_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X11] : k3_tarski(k1_zfmisc_1(X11)) = X11 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X6,X7] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_tarski(k3_tarski(X6),X7) )
      & ( ~ r1_tarski(esk1_2(X6,X7),X7)
        | r1_tarski(k3_tarski(X6),X7) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( ( ~ m1_setfam_1(X25,X24)
        | k5_setfam_1(X24,X25) = X24
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))) )
      & ( k5_setfam_1(X24,X25) != X24
        | m1_setfam_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).

cnf(c_0_23,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14)))
      | k5_setfam_1(X14,X15) = k3_tarski(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_29,plain,
    ( k5_setfam_1(X2,X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( m1_setfam_1(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_setfam_1(k1_zfmisc_1(X1),X2)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( m1_setfam_1(k1_zfmisc_1(X1),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r2_hidden(esk1_2(X1,k3_tarski(X2)),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k5_setfam_1(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_38,plain,(
    ! [X33] :
      ( ~ l1_pre_topc(X33)
      | m1_subset_1(u1_pre_topc(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_39,plain,(
    ! [X26,X27,X28,X29] :
      ( ( r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ r1_tarski(X27,u1_pre_topc(X26))
        | r2_hidden(k5_setfam_1(u1_struct_0(X26),X27),u1_pre_topc(X26))
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ r2_hidden(X28,u1_pre_topc(X26))
        | ~ r2_hidden(X29,u1_pre_topc(X26))
        | r2_hidden(k9_subset_1(u1_struct_0(X26),X28,X29),u1_pre_topc(X26))
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk3_1(X26),k1_zfmisc_1(u1_struct_0(X26)))
        | m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))
        | m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( r2_hidden(esk3_1(X26),u1_pre_topc(X26))
        | m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( r2_hidden(esk4_1(X26),u1_pre_topc(X26))
        | m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X26),esk3_1(X26),esk4_1(X26)),u1_pre_topc(X26))
        | m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk3_1(X26),k1_zfmisc_1(u1_struct_0(X26)))
        | r1_tarski(esk2_1(X26),u1_pre_topc(X26))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))
        | r1_tarski(esk2_1(X26),u1_pre_topc(X26))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( r2_hidden(esk3_1(X26),u1_pre_topc(X26))
        | r1_tarski(esk2_1(X26),u1_pre_topc(X26))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( r2_hidden(esk4_1(X26),u1_pre_topc(X26))
        | r1_tarski(esk2_1(X26),u1_pre_topc(X26))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X26),esk3_1(X26),esk4_1(X26)),u1_pre_topc(X26))
        | r1_tarski(esk2_1(X26),u1_pre_topc(X26))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk3_1(X26),k1_zfmisc_1(u1_struct_0(X26)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( r2_hidden(esk3_1(X26),u1_pre_topc(X26))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( r2_hidden(esk4_1(X26),u1_pre_topc(X26))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X26),esk3_1(X26),esk4_1(X26)),u1_pre_topc(X26))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))
        | ~ r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))
        | v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0))) != u1_struct_0(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( X1 = k3_tarski(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(k3_tarski(X1))
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_49,plain,(
    ! [X34] :
      ( v1_xboole_0(X34)
      | ~ r2_hidden(k3_tarski(X34),X34)
      | k4_yellow_0(k2_yellow_1(X34)) = k3_tarski(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_50,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_52,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_26])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk5_0)) = u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_47])])).

cnf(c_0_55,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0))) != u1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_xboole_0(u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_51])]),c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:05:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.15/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.15/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.15/0.40  #
% 0.15/0.40  # Preprocessing time       : 0.028 s
% 0.15/0.40  # Presaturation interreduction done
% 0.15/0.40  
% 0.15/0.40  # Proof found!
% 0.15/0.40  # SZS status Theorem
% 0.15/0.40  # SZS output start CNFRefutation
% 0.15/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.15/0.40  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.15/0.40  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.15/0.40  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.15/0.40  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.15/0.40  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.15/0.40  fof(t60_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 0.15/0.40  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.15/0.40  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.15/0.40  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.15/0.40  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.15/0.40  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.15/0.40  fof(c_0_12, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.15/0.40  fof(c_0_13, plain, ![X12, X13]:((~m1_setfam_1(X13,X12)|r1_tarski(X12,k3_tarski(X13)))&(~r1_tarski(X12,k3_tarski(X13))|m1_setfam_1(X13,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.15/0.40  fof(c_0_14, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|~v1_xboole_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.15/0.40  cnf(c_0_15, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.40  cnf(c_0_16, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.40  fof(c_0_17, plain, ![X4, X5]:(~r2_hidden(X4,X5)|r1_tarski(X4,k3_tarski(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.15/0.40  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.40  cnf(c_0_19, plain, (m1_subset_1(X1,k1_zfmisc_1(k3_tarski(X2)))|~m1_setfam_1(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.15/0.40  fof(c_0_20, plain, ![X11]:k3_tarski(k1_zfmisc_1(X11))=X11, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.15/0.40  fof(c_0_21, plain, ![X6, X7]:((r2_hidden(esk1_2(X6,X7),X6)|r1_tarski(k3_tarski(X6),X7))&(~r1_tarski(esk1_2(X6,X7),X7)|r1_tarski(k3_tarski(X6),X7))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.15/0.40  fof(c_0_22, plain, ![X24, X25]:((~m1_setfam_1(X25,X24)|k5_setfam_1(X24,X25)=X24|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))))&(k5_setfam_1(X24,X25)!=X24|m1_setfam_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).
% 0.15/0.40  cnf(c_0_23, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.40  cnf(c_0_24, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.40  cnf(c_0_25, plain, (~v1_xboole_0(k3_tarski(X1))|~m1_setfam_1(X1,X2)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.15/0.40  cnf(c_0_26, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.40  cnf(c_0_27, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.40  fof(c_0_28, plain, ![X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14)))|k5_setfam_1(X14,X15)=k3_tarski(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.15/0.40  cnf(c_0_29, plain, (k5_setfam_1(X2,X1)=X2|~m1_setfam_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.40  cnf(c_0_30, plain, (m1_setfam_1(X1,X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.15/0.40  fof(c_0_31, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.15/0.40  cnf(c_0_32, plain, (~v1_xboole_0(X1)|~m1_setfam_1(k1_zfmisc_1(X1),X2)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.15/0.40  cnf(c_0_33, plain, (m1_setfam_1(k1_zfmisc_1(X1),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_26])).
% 0.15/0.40  cnf(c_0_34, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r2_hidden(esk1_2(X1,k3_tarski(X2)),X2)), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.15/0.40  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.40  cnf(c_0_36, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.15/0.40  cnf(c_0_37, plain, (k5_setfam_1(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.15/0.40  fof(c_0_38, plain, ![X33]:(~l1_pre_topc(X33)|m1_subset_1(u1_pre_topc(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.15/0.40  fof(c_0_39, plain, ![X26, X27, X28, X29]:((((r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))|~v2_pre_topc(X26)|~l1_pre_topc(X26))&(~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|(~r1_tarski(X27,u1_pre_topc(X26))|r2_hidden(k5_setfam_1(u1_struct_0(X26),X27),u1_pre_topc(X26)))|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|(~r2_hidden(X28,u1_pre_topc(X26))|~r2_hidden(X29,u1_pre_topc(X26))|r2_hidden(k9_subset_1(u1_struct_0(X26),X28,X29),u1_pre_topc(X26))))|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(((m1_subset_1(esk3_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&((m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&(((r2_hidden(esk3_1(X26),u1_pre_topc(X26))|(m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&(r2_hidden(esk4_1(X26),u1_pre_topc(X26))|(m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r2_hidden(k9_subset_1(u1_struct_0(X26),esk3_1(X26),esk4_1(X26)),u1_pre_topc(X26))|(m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26)))))&(((m1_subset_1(esk3_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(r1_tarski(esk2_1(X26),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&((m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(r1_tarski(esk2_1(X26),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&(((r2_hidden(esk3_1(X26),u1_pre_topc(X26))|(r1_tarski(esk2_1(X26),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&(r2_hidden(esk4_1(X26),u1_pre_topc(X26))|(r1_tarski(esk2_1(X26),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r2_hidden(k9_subset_1(u1_struct_0(X26),esk3_1(X26),esk4_1(X26)),u1_pre_topc(X26))|(r1_tarski(esk2_1(X26),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26)))))&((m1_subset_1(esk3_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&((m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&(((r2_hidden(esk3_1(X26),u1_pre_topc(X26))|(~r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&(r2_hidden(esk4_1(X26),u1_pre_topc(X26))|(~r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r2_hidden(k9_subset_1(u1_struct_0(X26),esk3_1(X26),esk4_1(X26)),u1_pre_topc(X26))|(~r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.15/0.40  fof(c_0_40, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0)))!=u1_struct_0(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).
% 0.15/0.40  cnf(c_0_41, plain, (~v1_xboole_0(X1)|~r1_tarski(X2,X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.15/0.40  cnf(c_0_42, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.15/0.40  cnf(c_0_43, plain, (X1=k3_tarski(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.15/0.40  cnf(c_0_44, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.15/0.40  cnf(c_0_45, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.15/0.40  cnf(c_0_46, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.40  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.40  cnf(c_0_48, plain, (~v1_xboole_0(k3_tarski(X1))|~r2_hidden(X2,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.15/0.40  fof(c_0_49, plain, ![X34]:(v1_xboole_0(X34)|(~r2_hidden(k3_tarski(X34),X34)|k4_yellow_0(k2_yellow_1(X34))=k3_tarski(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.15/0.40  cnf(c_0_50, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.15/0.40  cnf(c_0_51, negated_conjecture, (r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.15/0.40  cnf(c_0_52, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_48, c_0_26])).
% 0.15/0.40  cnf(c_0_53, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.15/0.40  cnf(c_0_54, negated_conjecture, (k3_tarski(u1_pre_topc(esk5_0))=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_47])])).
% 0.15/0.40  cnf(c_0_55, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0)))!=u1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.40  cnf(c_0_56, negated_conjecture, (~v1_xboole_0(u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_52, c_0_51])).
% 0.15/0.40  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_51])]), c_0_55]), c_0_56]), ['proof']).
% 0.15/0.40  # SZS output end CNFRefutation
% 0.15/0.40  # Proof object total steps             : 58
% 0.15/0.40  # Proof object clause steps            : 33
% 0.15/0.40  # Proof object formula steps           : 25
% 0.15/0.40  # Proof object conjectures             : 10
% 0.15/0.40  # Proof object clause conjectures      : 7
% 0.15/0.40  # Proof object formula conjectures     : 3
% 0.15/0.40  # Proof object initial clauses used    : 16
% 0.15/0.40  # Proof object initial formulas used   : 12
% 0.15/0.40  # Proof object generating inferences   : 17
% 0.15/0.40  # Proof object simplifying inferences  : 8
% 0.15/0.40  # Training examples: 0 positive, 0 negative
% 0.15/0.40  # Parsed axioms                        : 14
% 0.15/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.40  # Initial clauses                      : 38
% 0.15/0.40  # Removed in clause preprocessing      : 0
% 0.15/0.40  # Initial clauses in saturation        : 38
% 0.15/0.40  # Processed clauses                    : 304
% 0.15/0.40  # ...of these trivial                  : 2
% 0.15/0.40  # ...subsumed                          : 100
% 0.15/0.40  # ...remaining for further processing  : 202
% 0.15/0.40  # Other redundant clauses eliminated   : 1
% 0.15/0.40  # Clauses deleted for lack of memory   : 0
% 0.15/0.40  # Backward-subsumed                    : 1
% 0.15/0.40  # Backward-rewritten                   : 1
% 0.15/0.40  # Generated clauses                    : 494
% 0.15/0.40  # ...of the previous two non-trivial   : 421
% 0.15/0.40  # Contextual simplify-reflections      : 1
% 0.15/0.40  # Paramodulations                      : 493
% 0.15/0.40  # Factorizations                       : 0
% 0.15/0.40  # Equation resolutions                 : 1
% 0.15/0.40  # Propositional unsat checks           : 0
% 0.15/0.40  #    Propositional check models        : 0
% 0.15/0.40  #    Propositional check unsatisfiable : 0
% 0.15/0.40  #    Propositional clauses             : 0
% 0.15/0.40  #    Propositional clauses after purity: 0
% 0.15/0.40  #    Propositional unsat core size     : 0
% 0.15/0.40  #    Propositional preprocessing time  : 0.000
% 0.15/0.40  #    Propositional encoding time       : 0.000
% 0.15/0.40  #    Propositional solver time         : 0.000
% 0.15/0.40  #    Success case prop preproc time    : 0.000
% 0.15/0.40  #    Success case prop encoding time   : 0.000
% 0.15/0.40  #    Success case prop solver time     : 0.000
% 0.15/0.40  # Current number of processed clauses  : 162
% 0.15/0.40  #    Positive orientable unit clauses  : 10
% 0.15/0.40  #    Positive unorientable unit clauses: 0
% 0.15/0.40  #    Negative unit clauses             : 3
% 0.15/0.40  #    Non-unit-clauses                  : 149
% 0.15/0.40  # Current number of unprocessed clauses: 169
% 0.15/0.40  # ...number of literals in the above   : 553
% 0.15/0.40  # Current number of archived formulas  : 0
% 0.15/0.40  # Current number of archived clauses   : 40
% 0.15/0.40  # Clause-clause subsumption calls (NU) : 4859
% 0.15/0.40  # Rec. Clause-clause subsumption calls : 2246
% 0.15/0.40  # Non-unit clause-clause subsumptions  : 101
% 0.15/0.40  # Unit Clause-clause subsumption calls : 134
% 0.15/0.40  # Rewrite failures with RHS unbound    : 0
% 0.15/0.40  # BW rewrite match attempts            : 38
% 0.15/0.40  # BW rewrite match successes           : 1
% 0.15/0.40  # Condensation attempts                : 0
% 0.15/0.40  # Condensation successes               : 0
% 0.15/0.40  # Termbank termtop insertions          : 10777
% 0.15/0.41  
% 0.15/0.41  # -------------------------------------------------
% 0.15/0.41  # User time                : 0.048 s
% 0.15/0.41  # System time              : 0.003 s
% 0.15/0.41  # Total time               : 0.051 s
% 0.15/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
