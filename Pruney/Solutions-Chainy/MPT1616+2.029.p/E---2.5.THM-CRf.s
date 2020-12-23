%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:00 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  158 (14703 expanded)
%              Number of clauses        :  129 (6651 expanded)
%              Number of leaves         :   14 (3660 expanded)
%              Depth                    :   37
%              Number of atoms          :  498 (68088 expanded)
%              Number of equality atoms :   29 (4014 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t56_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k3_tarski(X1),X2)
        & r2_hidden(X3,X1) )
     => r1_tarski(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t60_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(c_0_14,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_15,plain,(
    ! [X12,X13] :
      ( ( ~ m1_setfam_1(X13,X12)
        | r1_tarski(X12,k3_tarski(X13)) )
      & ( ~ r1_tarski(X12,k3_tarski(X13))
        | m1_setfam_1(X13,X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_16,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | ~ v1_xboole_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k3_tarski(X2)))
    | ~ m1_setfam_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_21,plain,(
    ! [X9] : k3_tarski(k1_zfmisc_1(X9)) = X9 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X4,X5] :
      ( ( r2_hidden(esk1_2(X4,X5),X4)
        | r1_tarski(k3_tarski(X4),X5) )
      & ( ~ r1_tarski(esk1_2(X4,X5),X5)
        | r1_tarski(k3_tarski(X4),X5) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

fof(c_0_23,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X11,X10)
        | r2_hidden(X11,X10)
        | v1_xboole_0(X10) )
      & ( ~ r2_hidden(X11,X10)
        | m1_subset_1(X11,X10)
        | v1_xboole_0(X10) )
      & ( ~ m1_subset_1(X11,X10)
        | v1_xboole_0(X11)
        | ~ v1_xboole_0(X10) )
      & ( ~ v1_xboole_0(X11)
        | m1_subset_1(X11,X10)
        | ~ v1_xboole_0(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_24,plain,
    ( ~ m1_setfam_1(X1,X2)
    | ~ v1_xboole_0(k3_tarski(X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_32,plain,
    ( ~ m1_setfam_1(k1_zfmisc_1(X1),X2)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( m1_setfam_1(k1_zfmisc_1(X1),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | v1_xboole_0(X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_36,plain,(
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

fof(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0))) != u1_struct_0(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_25])).

cnf(c_0_40,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk5_0)))
    | ~ v1_xboole_0(u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_47,plain,(
    ! [X33] :
      ( ~ l1_pre_topc(X33)
      | m1_subset_1(u1_pre_topc(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(esk5_0)))
    | ~ v1_xboole_0(u1_pre_topc(esk5_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | v1_xboole_0(u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_44])).

cnf(c_0_50,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(esk5_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_pre_topc(esk5_0)))
    | m1_subset_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_49])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_56,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_39])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_53]),c_0_49])).

cnf(c_0_58,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_50])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X1)
    | ~ m1_setfam_1(X2,X1)
    | ~ v1_xboole_0(k1_zfmisc_1(k3_tarski(X2))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_44]),c_0_42])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_44])).

cnf(c_0_62,plain,
    ( v1_xboole_0(u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_42])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | ~ m1_setfam_1(k1_zfmisc_1(X2),X1)
    | ~ v1_xboole_0(k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_25])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v1_xboole_0(u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk5_0))
    | r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_42])])).

cnf(c_0_68,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_33])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(u1_pre_topc(esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(esk5_0)))
    | r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(u1_pre_topc(esk5_0))
    | ~ r1_tarski(X1,u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_46])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k1_zfmisc_1(u1_pre_topc(esk5_0)),k1_zfmisc_1(u1_pre_topc(esk5_0)))
    | r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_46]),c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(X1)
    | r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ r1_tarski(X1,u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k3_tarski(u1_struct_0(esk5_0)),X1)
    | r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_30])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ r2_hidden(X1,k1_zfmisc_1(u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_73]),c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(k3_tarski(u1_struct_0(esk5_0)))
    | r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk5_0),X1)
    | r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_30]),c_0_25])).

fof(c_0_79,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(k3_tarski(X18),X19)
      | ~ r2_hidden(X20,X18)
      | r1_tarski(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).

fof(c_0_80,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | r1_tarski(k3_tarski(X7),k3_tarski(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ m1_setfam_1(u1_struct_0(esk5_0),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( m1_setfam_1(X1,u1_pre_topc(esk5_0))
    | r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_78])).

cnf(c_0_83,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_84,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_25])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_44])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_25])).

cnf(c_0_90,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r1_tarski(X2,k3_tarski(X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_39])).

cnf(c_0_91,plain,
    ( m1_setfam_1(X1,k3_tarski(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk5_0),X1)
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(esk5_0)),X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,plain,
    ( m1_setfam_1(X1,k3_tarski(X1))
    | v1_xboole_0(k1_zfmisc_1(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_94,plain,
    ( ~ v1_xboole_0(k3_tarski(X1))
    | ~ r1_tarski(k1_zfmisc_1(X2),X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_89])).

fof(c_0_95,plain,(
    ! [X24,X25] :
      ( ( ~ m1_setfam_1(X25,X24)
        | k5_setfam_1(X24,X25) = X24
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))) )
      & ( k5_setfam_1(X24,X25) != X24
        | m1_setfam_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk5_0)))
    | r1_tarski(u1_struct_0(esk5_0),k3_tarski(u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_44])).

cnf(c_0_97,plain,
    ( m1_setfam_1(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_25])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk5_0),k3_tarski(X1))
    | ~ m1_setfam_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_18])).

cnf(c_0_99,plain,
    ( m1_setfam_1(k1_zfmisc_1(X1),X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_25])).

cnf(c_0_100,plain,
    ( v1_xboole_0(u1_pre_topc(X1))
    | r1_tarski(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_39])).

cnf(c_0_101,plain,
    ( ~ m1_setfam_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(k3_tarski(k3_tarski(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_94,c_0_18])).

cnf(c_0_102,plain,
    ( k5_setfam_1(X2,X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( m1_setfam_1(u1_pre_topc(esk5_0),u1_struct_0(esk5_0))
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_96])).

cnf(c_0_104,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(k1_zfmisc_1(X2),k1_zfmisc_1(X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_97])).

cnf(c_0_105,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_25])).

cnf(c_0_106,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk5_0))
    | r1_tarski(k1_zfmisc_1(u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_42])).

cnf(c_0_107,plain,
    ( ~ m1_setfam_1(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ v1_xboole_0(k3_tarski(X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_25])).

cnf(c_0_108,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(X2))
    | ~ r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_97])).

cnf(c_0_109,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = u1_struct_0(esk5_0)
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk5_0)))
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_110,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_39])).

cnf(c_0_111,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X3,k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_91])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_105])).

cnf(c_0_113,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk5_0))
    | r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_106])).

cnf(c_0_114,plain,
    ( ~ v1_xboole_0(k3_tarski(X1))
    | ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(X2)),k1_zfmisc_1(X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_107,c_0_97])).

cnf(c_0_115,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_39])).

cnf(c_0_116,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = u1_struct_0(esk5_0)
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_50]),c_0_42])])).

cnf(c_0_117,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0))))
    | ~ v1_xboole_0(u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_44])).

cnf(c_0_118,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_28])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(k1_zfmisc_1(u1_pre_topc(esk5_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_46]),c_0_113])).

cnf(c_0_120,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_setfam_1(k1_zfmisc_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_25])).

cnf(c_0_121,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X1))))
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_39]),c_0_25])).

cnf(c_0_122,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = u1_struct_0(esk5_0)
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_25])).

cnf(c_0_124,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_97])).

cnf(c_0_125,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0)))))
    | ~ v1_xboole_0(u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_44])).

cnf(c_0_126,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = u1_struct_0(esk5_0)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0))))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_122])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_66]),c_0_113])).

cnf(c_0_128,plain,
    ( ~ v1_xboole_0(k3_tarski(X1))
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X3,k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_84])).

cnf(c_0_129,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_124,c_0_28])).

cnf(c_0_130,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0)))))
    | ~ v1_xboole_0(u1_pre_topc(esk5_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_125])).

fof(c_0_131,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14)))
      | k5_setfam_1(X14,X15) = k3_tarski(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_132,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = u1_struct_0(esk5_0)
    | m1_subset_1(k1_zfmisc_1(u1_pre_topc(esk5_0)),k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_116])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_127,c_0_44])).

cnf(c_0_134,plain,
    ( r1_tarski(k3_tarski(k3_tarski(X1)),X2)
    | ~ v1_xboole_0(k3_tarski(X3))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_128,c_0_30])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_pre_topc(esk5_0)))
    | ~ v1_xboole_0(u1_pre_topc(esk5_0))
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

fof(c_0_136,plain,(
    ! [X34] :
      ( v1_xboole_0(X34)
      | ~ r2_hidden(k3_tarski(X34),X34)
      | k4_yellow_0(k2_yellow_1(X34)) = k3_tarski(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_137,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_138,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_139,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = u1_struct_0(esk5_0)
    | r1_tarski(u1_pre_topc(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_132])).

cnf(c_0_140,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_133])).

cnf(c_0_141,plain,
    ( r1_tarski(k3_tarski(k3_tarski(X1)),X2)
    | ~ v1_xboole_0(X3)
    | ~ r1_tarski(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_134,c_0_25])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0))),k1_zfmisc_1(u1_pre_topc(esk5_0)))
    | ~ v1_xboole_0(u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_135,c_0_125])).

cnf(c_0_143,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_136])).

cnf(c_0_144,plain,
    ( r2_hidden(k3_tarski(X1),u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_145,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk5_0)) = u1_struct_0(esk5_0)
    | r1_tarski(u1_pre_topc(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_140])])).

cnf(c_0_146,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0))) != u1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk5_0),X1)
    | ~ v1_xboole_0(u1_pre_topc(esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_25]),c_0_25])).

cnf(c_0_148,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = k3_tarski(u1_pre_topc(X1))
    | v1_xboole_0(u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(u1_pre_topc(X1),u1_pre_topc(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_50])).

cnf(c_0_149,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_145]),c_0_44])]),c_0_146]),c_0_147])).

cnf(c_0_150,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = u1_struct_0(esk5_0)
    | v1_xboole_0(X1)
    | ~ r1_tarski(X1,u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_116])).

cnf(c_0_151,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0))) = k3_tarski(u1_pre_topc(esk5_0))
    | v1_xboole_0(u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_41]),c_0_42])])).

cnf(c_0_152,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) = u1_struct_0(esk5_0)
    | v1_xboole_0(u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_150,c_0_149])).

cnf(c_0_153,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk5_0))
    | k3_tarski(u1_pre_topc(esk5_0)) != u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_151])).

cnf(c_0_154,negated_conjecture,
    ( ~ v1_xboole_0(u1_pre_topc(esk5_0))
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_130]),c_0_117])).

cnf(c_0_155,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_152]),c_0_140])]),c_0_153])).

cnf(c_0_156,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154,c_0_155])])).

cnf(c_0_157,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_44]),c_0_155])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.40/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.40/0.58  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.40/0.58  #
% 0.40/0.58  # Preprocessing time       : 0.031 s
% 0.40/0.58  # Presaturation interreduction done
% 0.40/0.58  
% 0.40/0.58  # Proof found!
% 0.40/0.58  # SZS status Theorem
% 0.40/0.58  # SZS output start CNFRefutation
% 0.40/0.58  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.40/0.58  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.40/0.58  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.40/0.58  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.40/0.58  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.40/0.58  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.40/0.58  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.40/0.58  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.40/0.58  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.40/0.58  fof(t56_setfam_1, axiom, ![X1, X2, X3]:((r1_tarski(k3_tarski(X1),X2)&r2_hidden(X3,X1))=>r1_tarski(X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 0.40/0.58  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.40/0.58  fof(t60_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 0.40/0.58  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.40/0.58  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.40/0.58  fof(c_0_14, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.40/0.58  fof(c_0_15, plain, ![X12, X13]:((~m1_setfam_1(X13,X12)|r1_tarski(X12,k3_tarski(X13)))&(~r1_tarski(X12,k3_tarski(X13))|m1_setfam_1(X13,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.40/0.58  fof(c_0_16, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|~v1_xboole_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.40/0.58  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  cnf(c_0_18, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.40/0.58  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.58  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(k3_tarski(X2)))|~m1_setfam_1(X2,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.40/0.58  fof(c_0_21, plain, ![X9]:k3_tarski(k1_zfmisc_1(X9))=X9, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.40/0.58  fof(c_0_22, plain, ![X4, X5]:((r2_hidden(esk1_2(X4,X5),X4)|r1_tarski(k3_tarski(X4),X5))&(~r1_tarski(esk1_2(X4,X5),X5)|r1_tarski(k3_tarski(X4),X5))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.40/0.58  fof(c_0_23, plain, ![X10, X11]:(((~m1_subset_1(X11,X10)|r2_hidden(X11,X10)|v1_xboole_0(X10))&(~r2_hidden(X11,X10)|m1_subset_1(X11,X10)|v1_xboole_0(X10)))&((~m1_subset_1(X11,X10)|v1_xboole_0(X11)|~v1_xboole_0(X10))&(~v1_xboole_0(X11)|m1_subset_1(X11,X10)|~v1_xboole_0(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.40/0.58  cnf(c_0_24, plain, (~m1_setfam_1(X1,X2)|~v1_xboole_0(k3_tarski(X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.40/0.58  cnf(c_0_25, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.40/0.58  cnf(c_0_26, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.40/0.58  cnf(c_0_27, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.40/0.58  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  cnf(c_0_29, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.40/0.58  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.40/0.58  fof(c_0_31, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.40/0.58  cnf(c_0_32, plain, (~m1_setfam_1(k1_zfmisc_1(X1),X2)|~v1_xboole_0(X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.40/0.58  cnf(c_0_33, plain, (m1_setfam_1(k1_zfmisc_1(X1),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.40/0.58  cnf(c_0_34, plain, (r1_tarski(k3_tarski(X1),X2)|~m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.40/0.58  cnf(c_0_35, plain, (m1_subset_1(esk1_2(X1,X2),X1)|v1_xboole_0(X1)|r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.40/0.58  fof(c_0_36, plain, ![X26, X27, X28, X29]:((((r2_hidden(u1_struct_0(X26),u1_pre_topc(X26))|~v2_pre_topc(X26)|~l1_pre_topc(X26))&(~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|(~r1_tarski(X27,u1_pre_topc(X26))|r2_hidden(k5_setfam_1(u1_struct_0(X26),X27),u1_pre_topc(X26)))|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|(~r2_hidden(X28,u1_pre_topc(X26))|~r2_hidden(X29,u1_pre_topc(X26))|r2_hidden(k9_subset_1(u1_struct_0(X26),X28,X29),u1_pre_topc(X26))))|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(((m1_subset_1(esk3_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&((m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&(((r2_hidden(esk3_1(X26),u1_pre_topc(X26))|(m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&(r2_hidden(esk4_1(X26),u1_pre_topc(X26))|(m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r2_hidden(k9_subset_1(u1_struct_0(X26),esk3_1(X26),esk4_1(X26)),u1_pre_topc(X26))|(m1_subset_1(esk2_1(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26)))))&(((m1_subset_1(esk3_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(r1_tarski(esk2_1(X26),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&((m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(r1_tarski(esk2_1(X26),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&(((r2_hidden(esk3_1(X26),u1_pre_topc(X26))|(r1_tarski(esk2_1(X26),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&(r2_hidden(esk4_1(X26),u1_pre_topc(X26))|(r1_tarski(esk2_1(X26),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r2_hidden(k9_subset_1(u1_struct_0(X26),esk3_1(X26),esk4_1(X26)),u1_pre_topc(X26))|(r1_tarski(esk2_1(X26),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26)))))&((m1_subset_1(esk3_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&((m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&(((r2_hidden(esk3_1(X26),u1_pre_topc(X26))|(~r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26))&(r2_hidden(esk4_1(X26),u1_pre_topc(X26))|(~r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r2_hidden(k9_subset_1(u1_struct_0(X26),esk3_1(X26),esk4_1(X26)),u1_pre_topc(X26))|(~r2_hidden(k5_setfam_1(u1_struct_0(X26),esk2_1(X26)),u1_pre_topc(X26))|~r2_hidden(u1_struct_0(X26),u1_pre_topc(X26)))|v2_pre_topc(X26)|~l1_pre_topc(X26)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.40/0.58  fof(c_0_37, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0)))!=u1_struct_0(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).
% 0.40/0.58  cnf(c_0_38, plain, (~v1_xboole_0(X1)|~r1_tarski(X2,X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.40/0.58  cnf(c_0_39, plain, (v1_xboole_0(k1_zfmisc_1(X1))|r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_25])).
% 0.40/0.58  cnf(c_0_40, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.40/0.58  cnf(c_0_41, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.40/0.58  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.40/0.58  cnf(c_0_43, plain, (v1_xboole_0(k1_zfmisc_1(X1))|~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.40/0.58  cnf(c_0_44, negated_conjecture, (r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.40/0.58  cnf(c_0_45, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.40/0.58  cnf(c_0_46, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk5_0)))|~v1_xboole_0(u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.40/0.58  fof(c_0_47, plain, ![X33]:(~l1_pre_topc(X33)|m1_subset_1(u1_pre_topc(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.40/0.58  cnf(c_0_48, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(esk5_0)))|~v1_xboole_0(u1_pre_topc(esk5_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.40/0.58  cnf(c_0_49, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))|v1_xboole_0(u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_29, c_0_44])).
% 0.40/0.58  cnf(c_0_50, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.40/0.58  cnf(c_0_51, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))|m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(esk5_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.40/0.58  cnf(c_0_52, plain, (~l1_pre_topc(X1)|~v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_19, c_0_50])).
% 0.40/0.58  cnf(c_0_53, negated_conjecture, (m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_pre_topc(esk5_0)))|m1_subset_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_49])).
% 0.40/0.58  cnf(c_0_54, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.40/0.58  cnf(c_0_55, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.40/0.58  cnf(c_0_56, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X1))|~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_52, c_0_39])).
% 0.40/0.58  cnf(c_0_57, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))|~r2_hidden(X1,u1_pre_topc(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_53]), c_0_49])).
% 0.40/0.58  cnf(c_0_58, plain, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_54, c_0_50])).
% 0.40/0.58  cnf(c_0_59, plain, (v1_xboole_0(X1)|~m1_setfam_1(X2,X1)|~v1_xboole_0(k1_zfmisc_1(k3_tarski(X2)))), inference(spm,[status(thm)],[c_0_55, c_0_20])).
% 0.40/0.58  cnf(c_0_60, negated_conjecture, (r1_tarski(u1_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_44]), c_0_42])])).
% 0.40/0.58  cnf(c_0_61, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_57, c_0_44])).
% 0.40/0.58  cnf(c_0_62, plain, (v1_xboole_0(u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_55, c_0_50])).
% 0.40/0.58  cnf(c_0_63, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))|r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_58, c_0_42])).
% 0.40/0.58  cnf(c_0_64, plain, (v1_xboole_0(X1)|~m1_setfam_1(k1_zfmisc_1(X2),X1)|~v1_xboole_0(k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_59, c_0_25])).
% 0.40/0.58  cnf(c_0_65, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_60])).
% 0.40/0.58  cnf(c_0_66, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~v1_xboole_0(u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_55, c_0_61])).
% 0.40/0.58  cnf(c_0_67, negated_conjecture, (v1_xboole_0(u1_pre_topc(esk5_0))|r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_42])])).
% 0.40/0.58  cnf(c_0_68, plain, (v1_xboole_0(X1)|~v1_xboole_0(k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_64, c_0_33])).
% 0.40/0.58  cnf(c_0_69, negated_conjecture, (~v1_xboole_0(u1_pre_topc(esk5_0))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.40/0.58  cnf(c_0_70, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(esk5_0)))|r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_67])).
% 0.40/0.58  cnf(c_0_71, negated_conjecture, (v1_xboole_0(X1)|~v1_xboole_0(u1_pre_topc(esk5_0))|~r1_tarski(X1,u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_68, c_0_46])).
% 0.40/0.58  cnf(c_0_72, negated_conjecture, (r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_69, c_0_67])).
% 0.40/0.58  cnf(c_0_73, negated_conjecture, (m1_subset_1(k1_zfmisc_1(u1_pre_topc(esk5_0)),k1_zfmisc_1(u1_pre_topc(esk5_0)))|r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_46]), c_0_67])).
% 0.40/0.58  cnf(c_0_74, negated_conjecture, (v1_xboole_0(X1)|r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))|~r1_tarski(X1,u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_71, c_0_67])).
% 0.40/0.58  cnf(c_0_75, negated_conjecture, (r1_tarski(k3_tarski(u1_struct_0(esk5_0)),X1)|r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_72, c_0_30])).
% 0.40/0.58  cnf(c_0_76, negated_conjecture, (r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))|~r2_hidden(X1,k1_zfmisc_1(u1_pre_topc(esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_73]), c_0_67])).
% 0.40/0.58  cnf(c_0_77, negated_conjecture, (v1_xboole_0(k3_tarski(u1_struct_0(esk5_0)))|r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.40/0.58  cnf(c_0_78, negated_conjecture, (r1_tarski(u1_pre_topc(esk5_0),X1)|r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_30]), c_0_25])).
% 0.40/0.58  fof(c_0_79, plain, ![X18, X19, X20]:(~r1_tarski(k3_tarski(X18),X19)|~r2_hidden(X20,X18)|r1_tarski(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).
% 0.40/0.58  fof(c_0_80, plain, ![X7, X8]:(~r1_tarski(X7,X8)|r1_tarski(k3_tarski(X7),k3_tarski(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.40/0.58  cnf(c_0_81, negated_conjecture, (r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))|~m1_setfam_1(u1_struct_0(esk5_0),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_77])).
% 0.40/0.58  cnf(c_0_82, negated_conjecture, (m1_setfam_1(X1,u1_pre_topc(esk5_0))|r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_26, c_0_78])).
% 0.40/0.58  cnf(c_0_83, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.40/0.58  cnf(c_0_84, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.40/0.58  cnf(c_0_85, negated_conjecture, (r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))|~r2_hidden(X1,u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.40/0.58  cnf(c_0_86, plain, (r1_tarski(X1,k3_tarski(X2))|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.40/0.58  cnf(c_0_87, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_83, c_0_25])).
% 0.40/0.58  cnf(c_0_88, negated_conjecture, (r2_hidden(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_85, c_0_44])).
% 0.40/0.58  cnf(c_0_89, plain, (r1_tarski(X1,k3_tarski(X2))|~r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_84, c_0_25])).
% 0.40/0.58  cnf(c_0_90, plain, (v1_xboole_0(k1_zfmisc_1(X1))|r1_tarski(X2,k3_tarski(X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_86, c_0_39])).
% 0.40/0.58  cnf(c_0_91, plain, (m1_setfam_1(X1,k3_tarski(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_84])).
% 0.40/0.58  cnf(c_0_92, negated_conjecture, (r1_tarski(u1_pre_topc(esk5_0),X1)|~r1_tarski(k1_zfmisc_1(u1_struct_0(esk5_0)),X1)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.40/0.58  cnf(c_0_93, plain, (m1_setfam_1(X1,k3_tarski(X1))|v1_xboole_0(k1_zfmisc_1(k3_tarski(X1)))), inference(spm,[status(thm)],[c_0_26, c_0_39])).
% 0.40/0.58  cnf(c_0_94, plain, (~v1_xboole_0(k3_tarski(X1))|~r1_tarski(k1_zfmisc_1(X2),X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_38, c_0_89])).
% 0.40/0.58  fof(c_0_95, plain, ![X24, X25]:((~m1_setfam_1(X25,X24)|k5_setfam_1(X24,X25)=X24|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))))&(k5_setfam_1(X24,X25)!=X24|m1_setfam_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).
% 0.40/0.58  cnf(c_0_96, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk5_0)))|r1_tarski(u1_struct_0(esk5_0),k3_tarski(u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_90, c_0_44])).
% 0.40/0.58  cnf(c_0_97, plain, (m1_setfam_1(X1,X2)|~r1_tarski(k1_zfmisc_1(X2),X1)), inference(spm,[status(thm)],[c_0_91, c_0_25])).
% 0.40/0.58  cnf(c_0_98, negated_conjecture, (r1_tarski(u1_pre_topc(esk5_0),k3_tarski(X1))|~m1_setfam_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_92, c_0_18])).
% 0.40/0.58  cnf(c_0_99, plain, (m1_setfam_1(k1_zfmisc_1(X1),X1)|v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_93, c_0_25])).
% 0.40/0.58  cnf(c_0_100, plain, (v1_xboole_0(u1_pre_topc(X1))|r1_tarski(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_62, c_0_39])).
% 0.40/0.58  cnf(c_0_101, plain, (~m1_setfam_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(k3_tarski(k3_tarski(X1)))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_94, c_0_18])).
% 0.40/0.58  cnf(c_0_102, plain, (k5_setfam_1(X2,X1)=X2|~m1_setfam_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.40/0.58  cnf(c_0_103, negated_conjecture, (m1_setfam_1(u1_pre_topc(esk5_0),u1_struct_0(esk5_0))|v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_26, c_0_96])).
% 0.40/0.58  cnf(c_0_104, plain, (~v1_xboole_0(X1)|~r1_tarski(k1_zfmisc_1(X2),k1_zfmisc_1(X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_32, c_0_97])).
% 0.40/0.58  cnf(c_0_105, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))|r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_25])).
% 0.40/0.58  cnf(c_0_106, negated_conjecture, (v1_xboole_0(u1_pre_topc(esk5_0))|r1_tarski(k1_zfmisc_1(u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_100, c_0_42])).
% 0.40/0.58  cnf(c_0_107, plain, (~m1_setfam_1(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~v1_xboole_0(k3_tarski(X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_101, c_0_25])).
% 0.40/0.58  cnf(c_0_108, plain, (v1_xboole_0(X1)|~v1_xboole_0(k1_zfmisc_1(X2))|~r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_64, c_0_97])).
% 0.40/0.58  cnf(c_0_109, negated_conjecture, (k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=u1_struct_0(esk5_0)|v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk5_0)))|~m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.40/0.58  cnf(c_0_110, plain, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X1)))|~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_104, c_0_39])).
% 0.40/0.58  cnf(c_0_111, plain, (~v1_xboole_0(X1)|~r1_tarski(X2,k1_zfmisc_1(X1))|~r2_hidden(X3,k3_tarski(X2))), inference(spm,[status(thm)],[c_0_32, c_0_91])).
% 0.40/0.58  cnf(c_0_112, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))|r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_45, c_0_105])).
% 0.40/0.58  cnf(c_0_113, negated_conjecture, (v1_xboole_0(u1_pre_topc(esk5_0))|r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_92, c_0_106])).
% 0.40/0.58  cnf(c_0_114, plain, (~v1_xboole_0(k3_tarski(X1))|~r1_tarski(k1_zfmisc_1(k1_zfmisc_1(X2)),k1_zfmisc_1(X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_107, c_0_97])).
% 0.40/0.58  cnf(c_0_115, plain, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X1)))|v1_xboole_0(X1)|~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_108, c_0_39])).
% 0.40/0.58  cnf(c_0_116, negated_conjecture, (k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=u1_struct_0(esk5_0)|v1_xboole_0(k1_zfmisc_1(u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_50]), c_0_42])])).
% 0.40/0.58  cnf(c_0_117, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0))))|~v1_xboole_0(u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_110, c_0_44])).
% 0.40/0.58  cnf(c_0_118, plain, (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~v1_xboole_0(X2)|~r2_hidden(X3,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_111, c_0_28])).
% 0.40/0.58  cnf(c_0_119, negated_conjecture, (m1_subset_1(k1_zfmisc_1(u1_pre_topc(esk5_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))|r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_46]), c_0_113])).
% 0.40/0.58  cnf(c_0_120, plain, (r1_tarski(X1,X2)|~m1_setfam_1(k1_zfmisc_1(X2),X1)), inference(spm,[status(thm)],[c_0_18, c_0_25])).
% 0.40/0.58  cnf(c_0_121, plain, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X1))))|~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_39]), c_0_25])).
% 0.40/0.58  cnf(c_0_122, negated_conjecture, (k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=u1_struct_0(esk5_0)|v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117])).
% 0.40/0.58  cnf(c_0_123, negated_conjecture, (r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_xboole_0(u1_struct_0(esk5_0))|~r2_hidden(X1,u1_pre_topc(esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_25])).
% 0.40/0.58  cnf(c_0_124, plain, (r1_tarski(X1,X2)|~r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_120, c_0_97])).
% 0.40/0.58  cnf(c_0_125, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0)))))|~v1_xboole_0(u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_121, c_0_44])).
% 0.40/0.58  cnf(c_0_126, negated_conjecture, (k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=u1_struct_0(esk5_0)|m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0))))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_45, c_0_122])).
% 0.40/0.58  cnf(c_0_127, negated_conjecture, (r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X1,u1_pre_topc(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_66]), c_0_113])).
% 0.40/0.58  cnf(c_0_128, plain, (~v1_xboole_0(k3_tarski(X1))|~r1_tarski(X2,X1)|~r2_hidden(X3,k3_tarski(X2))), inference(spm,[status(thm)],[c_0_38, c_0_84])).
% 0.40/0.58  cnf(c_0_129, plain, (r1_tarski(X1,X2)|~m1_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_124, c_0_28])).
% 0.40/0.58  cnf(c_0_130, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0)))))|~v1_xboole_0(u1_pre_topc(esk5_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_45, c_0_125])).
% 0.40/0.58  fof(c_0_131, plain, ![X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14)))|k5_setfam_1(X14,X15)=k3_tarski(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.40/0.58  cnf(c_0_132, negated_conjecture, (k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=u1_struct_0(esk5_0)|m1_subset_1(k1_zfmisc_1(u1_pre_topc(esk5_0)),k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0))))), inference(spm,[status(thm)],[c_0_126, c_0_116])).
% 0.40/0.58  cnf(c_0_133, negated_conjecture, (r1_tarski(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_127, c_0_44])).
% 0.40/0.58  cnf(c_0_134, plain, (r1_tarski(k3_tarski(k3_tarski(X1)),X2)|~v1_xboole_0(k3_tarski(X3))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_128, c_0_30])).
% 0.40/0.58  cnf(c_0_135, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(u1_pre_topc(esk5_0)))|~v1_xboole_0(u1_pre_topc(esk5_0))|~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 0.40/0.58  fof(c_0_136, plain, ![X34]:(v1_xboole_0(X34)|(~r2_hidden(k3_tarski(X34),X34)|k4_yellow_0(k2_yellow_1(X34))=k3_tarski(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.40/0.58  cnf(c_0_137, plain, (r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r1_tarski(X1,u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.40/0.58  cnf(c_0_138, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_131])).
% 0.40/0.58  cnf(c_0_139, negated_conjecture, (k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=u1_struct_0(esk5_0)|r1_tarski(u1_pre_topc(esk5_0),u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_129, c_0_132])).
% 0.40/0.58  cnf(c_0_140, negated_conjecture, (m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_17, c_0_133])).
% 0.40/0.58  cnf(c_0_141, plain, (r1_tarski(k3_tarski(k3_tarski(X1)),X2)|~v1_xboole_0(X3)|~r1_tarski(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_134, c_0_25])).
% 0.40/0.58  cnf(c_0_142, negated_conjecture, (r1_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(esk5_0))),k1_zfmisc_1(u1_pre_topc(esk5_0)))|~v1_xboole_0(u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_135, c_0_125])).
% 0.40/0.58  cnf(c_0_143, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_136])).
% 0.40/0.58  cnf(c_0_144, plain, (r2_hidden(k3_tarski(X1),u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r1_tarski(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 0.40/0.58  cnf(c_0_145, negated_conjecture, (k3_tarski(u1_pre_topc(esk5_0))=u1_struct_0(esk5_0)|r1_tarski(u1_pre_topc(esk5_0),u1_pre_topc(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_139]), c_0_140])])).
% 0.40/0.58  cnf(c_0_146, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0)))!=u1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.40/0.58  cnf(c_0_147, negated_conjecture, (r1_tarski(u1_pre_topc(esk5_0),X1)|~v1_xboole_0(u1_pre_topc(esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_25]), c_0_25])).
% 0.40/0.58  cnf(c_0_148, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=k3_tarski(u1_pre_topc(X1))|v1_xboole_0(u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r1_tarski(u1_pre_topc(X1),u1_pre_topc(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_50])).
% 0.40/0.58  cnf(c_0_149, negated_conjecture, (r1_tarski(u1_pre_topc(esk5_0),u1_pre_topc(esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_145]), c_0_44])]), c_0_146]), c_0_147])).
% 0.40/0.58  cnf(c_0_150, negated_conjecture, (k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=u1_struct_0(esk5_0)|v1_xboole_0(X1)|~r1_tarski(X1,u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_68, c_0_116])).
% 0.40/0.58  cnf(c_0_151, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0)))=k3_tarski(u1_pre_topc(esk5_0))|v1_xboole_0(u1_pre_topc(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_41]), c_0_42])])).
% 0.40/0.58  cnf(c_0_152, negated_conjecture, (k5_setfam_1(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))=u1_struct_0(esk5_0)|v1_xboole_0(u1_pre_topc(esk5_0))), inference(spm,[status(thm)],[c_0_150, c_0_149])).
% 0.40/0.58  cnf(c_0_153, negated_conjecture, (v1_xboole_0(u1_pre_topc(esk5_0))|k3_tarski(u1_pre_topc(esk5_0))!=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_146, c_0_151])).
% 0.40/0.58  cnf(c_0_154, negated_conjecture, (~v1_xboole_0(u1_pre_topc(esk5_0))|~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_130]), c_0_117])).
% 0.40/0.58  cnf(c_0_155, negated_conjecture, (v1_xboole_0(u1_pre_topc(esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_152]), c_0_140])]), c_0_153])).
% 0.40/0.58  cnf(c_0_156, negated_conjecture, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154, c_0_155])])).
% 0.40/0.58  cnf(c_0_157, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_44]), c_0_155])]), ['proof']).
% 0.40/0.58  # SZS output end CNFRefutation
% 0.40/0.58  # Proof object total steps             : 158
% 0.40/0.58  # Proof object clause steps            : 129
% 0.40/0.58  # Proof object formula steps           : 29
% 0.40/0.58  # Proof object conjectures             : 68
% 0.40/0.58  # Proof object clause conjectures      : 65
% 0.40/0.58  # Proof object formula conjectures     : 3
% 0.40/0.58  # Proof object initial clauses used    : 23
% 0.40/0.58  # Proof object initial formulas used   : 14
% 0.40/0.58  # Proof object generating inferences   : 105
% 0.40/0.58  # Proof object simplifying inferences  : 39
% 0.40/0.58  # Training examples: 0 positive, 0 negative
% 0.40/0.58  # Parsed axioms                        : 14
% 0.40/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.58  # Initial clauses                      : 41
% 0.40/0.58  # Removed in clause preprocessing      : 0
% 0.40/0.58  # Initial clauses in saturation        : 41
% 0.40/0.58  # Processed clauses                    : 2406
% 0.40/0.58  # ...of these trivial                  : 4
% 0.40/0.58  # ...subsumed                          : 1301
% 0.40/0.58  # ...remaining for further processing  : 1101
% 0.40/0.58  # Other redundant clauses eliminated   : 2
% 0.40/0.58  # Clauses deleted for lack of memory   : 0
% 0.40/0.58  # Backward-subsumed                    : 115
% 0.40/0.58  # Backward-rewritten                   : 415
% 0.40/0.58  # Generated clauses                    : 8407
% 0.40/0.58  # ...of the previous two non-trivial   : 7898
% 0.40/0.58  # Contextual simplify-reflections      : 65
% 0.40/0.58  # Paramodulations                      : 8403
% 0.40/0.58  # Factorizations                       : 2
% 0.40/0.58  # Equation resolutions                 : 2
% 0.40/0.58  # Propositional unsat checks           : 0
% 0.40/0.58  #    Propositional check models        : 0
% 0.40/0.58  #    Propositional check unsatisfiable : 0
% 0.40/0.58  #    Propositional clauses             : 0
% 0.40/0.58  #    Propositional clauses after purity: 0
% 0.40/0.58  #    Propositional unsat core size     : 0
% 0.40/0.58  #    Propositional preprocessing time  : 0.000
% 0.40/0.58  #    Propositional encoding time       : 0.000
% 0.40/0.58  #    Propositional solver time         : 0.000
% 0.40/0.58  #    Success case prop preproc time    : 0.000
% 0.40/0.58  #    Success case prop encoding time   : 0.000
% 0.40/0.58  #    Success case prop solver time     : 0.000
% 0.40/0.58  # Current number of processed clauses  : 530
% 0.40/0.58  #    Positive orientable unit clauses  : 19
% 0.40/0.58  #    Positive unorientable unit clauses: 0
% 0.40/0.58  #    Negative unit clauses             : 2
% 0.40/0.58  #    Non-unit-clauses                  : 509
% 0.40/0.58  # Current number of unprocessed clauses: 5374
% 0.40/0.58  # ...number of literals in the above   : 19114
% 0.40/0.58  # Current number of archived formulas  : 0
% 0.40/0.58  # Current number of archived clauses   : 571
% 0.40/0.58  # Clause-clause subsumption calls (NU) : 68078
% 0.40/0.58  # Rec. Clause-clause subsumption calls : 33862
% 0.40/0.58  # Non-unit clause-clause subsumptions  : 1458
% 0.40/0.58  # Unit Clause-clause subsumption calls : 495
% 0.40/0.58  # Rewrite failures with RHS unbound    : 0
% 0.40/0.58  # BW rewrite match attempts            : 16
% 0.40/0.58  # BW rewrite match successes           : 16
% 0.40/0.58  # Condensation attempts                : 0
% 0.40/0.58  # Condensation successes               : 0
% 0.40/0.58  # Termbank termtop insertions          : 142008
% 0.40/0.58  
% 0.40/0.58  # -------------------------------------------------
% 0.40/0.58  # User time                : 0.229 s
% 0.40/0.58  # System time              : 0.009 s
% 0.40/0.58  # Total time               : 0.238 s
% 0.40/0.58  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
