%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:00 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of clauses        :   27 (  31 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  219 ( 480 expanded)
%              Number of equality atoms :   21 (  36 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

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

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(c_0_10,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(k3_tarski(X11),X12)
      | ~ r2_hidden(X13,X11)
      | r1_tarski(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(k3_tarski(X6),k3_tarski(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_16,plain,(
    ! [X8] : k3_tarski(k1_zfmisc_1(X8)) = X8 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_22,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | m1_subset_1(u1_pre_topc(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_23,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X16))
      | ~ v1_xboole_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_24,plain,
    ( k3_tarski(X1) = X2
    | ~ r2_hidden(X2,X1)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X17,X18,X19,X20] :
      ( ( r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
        | ~ r1_tarski(X18,u1_pre_topc(X17))
        | r2_hidden(k5_setfam_1(u1_struct_0(X17),X18),u1_pre_topc(X17))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r2_hidden(X19,u1_pre_topc(X17))
        | ~ r2_hidden(X20,u1_pre_topc(X17))
        | r2_hidden(k9_subset_1(u1_struct_0(X17),X19,X20),u1_pre_topc(X17))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk2_1(X17),k1_zfmisc_1(u1_struct_0(X17)))
        | m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk3_1(X17),k1_zfmisc_1(u1_struct_0(X17)))
        | m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk2_1(X17),u1_pre_topc(X17))
        | m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk3_1(X17),u1_pre_topc(X17))
        | m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X17),esk2_1(X17),esk3_1(X17)),u1_pre_topc(X17))
        | m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk2_1(X17),k1_zfmisc_1(u1_struct_0(X17)))
        | r1_tarski(esk1_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk3_1(X17),k1_zfmisc_1(u1_struct_0(X17)))
        | r1_tarski(esk1_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk2_1(X17),u1_pre_topc(X17))
        | r1_tarski(esk1_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk3_1(X17),u1_pre_topc(X17))
        | r1_tarski(esk1_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X17),esk2_1(X17),esk3_1(X17)),u1_pre_topc(X17))
        | r1_tarski(esk1_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk2_1(X17),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk3_1(X17),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk2_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk3_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X17),esk2_1(X17),esk3_1(X17)),u1_pre_topc(X17))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_31,plain,
    ( k3_tarski(X1) = X2
    | ~ r2_hidden(X2,X1)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(u1_pre_topc(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

fof(c_0_36,plain,(
    ! [X25] :
      ( v1_xboole_0(X25)
      | ~ r2_hidden(k3_tarski(X25),X25)
      | k4_yellow_0(k2_yellow_1(X25)) = k3_tarski(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_37,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(u1_pre_topc(X1),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk4_0))) != u1_struct_0(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_35])])])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_42,plain,
    ( ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk4_0))) != u1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_34]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.37  fof(t56_setfam_1, axiom, ![X1, X2, X3]:((r1_tarski(k3_tarski(X1),X2)&r2_hidden(X3,X1))=>r1_tarski(X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 0.13/0.37  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.13/0.37  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.13/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.37  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.13/0.37  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.13/0.37  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.13/0.37  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.13/0.37  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.13/0.37  fof(c_0_10, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.37  fof(c_0_11, plain, ![X11, X12, X13]:(~r1_tarski(k3_tarski(X11),X12)|~r2_hidden(X13,X11)|r1_tarski(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).
% 0.13/0.37  cnf(c_0_12, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_13, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_14, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_15, plain, ![X6, X7]:(~r1_tarski(X6,X7)|r1_tarski(k3_tarski(X6),k3_tarski(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.13/0.38  fof(c_0_16, plain, ![X8]:k3_tarski(k1_zfmisc_1(X8))=X8, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.13/0.38  cnf(c_0_17, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_18, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  cnf(c_0_19, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_20, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_21, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  fof(c_0_22, plain, ![X24]:(~l1_pre_topc(X24)|m1_subset_1(u1_pre_topc(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.13/0.38  fof(c_0_23, plain, ![X14, X15, X16]:(~r2_hidden(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X16))|~v1_xboole_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.13/0.38  cnf(c_0_24, plain, (k3_tarski(X1)=X2|~r2_hidden(X2,X1)|~r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_25, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.38  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_27, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  fof(c_0_30, plain, ![X17, X18, X19, X20]:((((r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))|~v2_pre_topc(X17)|~l1_pre_topc(X17))&(~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|(~r1_tarski(X18,u1_pre_topc(X17))|r2_hidden(k5_setfam_1(u1_struct_0(X17),X18),u1_pre_topc(X17)))|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))|(~r2_hidden(X19,u1_pre_topc(X17))|~r2_hidden(X20,u1_pre_topc(X17))|r2_hidden(k9_subset_1(u1_struct_0(X17),X19,X20),u1_pre_topc(X17))))|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(((m1_subset_1(esk2_1(X17),k1_zfmisc_1(u1_struct_0(X17)))|(m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&((m1_subset_1(esk3_1(X17),k1_zfmisc_1(u1_struct_0(X17)))|(m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&(((r2_hidden(esk2_1(X17),u1_pre_topc(X17))|(m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&(r2_hidden(esk3_1(X17),u1_pre_topc(X17))|(m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17)))&(~r2_hidden(k9_subset_1(u1_struct_0(X17),esk2_1(X17),esk3_1(X17)),u1_pre_topc(X17))|(m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17)))))&(((m1_subset_1(esk2_1(X17),k1_zfmisc_1(u1_struct_0(X17)))|(r1_tarski(esk1_1(X17),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&((m1_subset_1(esk3_1(X17),k1_zfmisc_1(u1_struct_0(X17)))|(r1_tarski(esk1_1(X17),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&(((r2_hidden(esk2_1(X17),u1_pre_topc(X17))|(r1_tarski(esk1_1(X17),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&(r2_hidden(esk3_1(X17),u1_pre_topc(X17))|(r1_tarski(esk1_1(X17),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17)))&(~r2_hidden(k9_subset_1(u1_struct_0(X17),esk2_1(X17),esk3_1(X17)),u1_pre_topc(X17))|(r1_tarski(esk1_1(X17),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17)))))&((m1_subset_1(esk2_1(X17),k1_zfmisc_1(u1_struct_0(X17)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&((m1_subset_1(esk3_1(X17),k1_zfmisc_1(u1_struct_0(X17)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&(((r2_hidden(esk2_1(X17),u1_pre_topc(X17))|(~r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&(r2_hidden(esk3_1(X17),u1_pre_topc(X17))|(~r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17)))&(~r2_hidden(k9_subset_1(u1_struct_0(X17),esk2_1(X17),esk3_1(X17)),u1_pre_topc(X17))|(~r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.13/0.38  cnf(c_0_31, plain, (k3_tarski(X1)=X2|~r2_hidden(X2,X1)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  cnf(c_0_32, plain, (r1_tarski(u1_pre_topc(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_33, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_34, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  fof(c_0_35, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.13/0.38  fof(c_0_36, plain, ![X25]:(v1_xboole_0(X25)|(~r2_hidden(k3_tarski(X25),X25)|k4_yellow_0(k2_yellow_1(X25))=k3_tarski(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.13/0.38  cnf(c_0_37, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.38  cnf(c_0_38, plain, (~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(X2)|~r1_tarski(u1_pre_topc(X1),X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.38  fof(c_0_39, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk4_0)))!=u1_struct_0(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_35])])])])).
% 0.13/0.38  cnf(c_0_40, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_41, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_37, c_0_34])).
% 0.13/0.38  cnf(c_0_42, plain, (~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_38, c_0_14])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk4_0)))!=u1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_44, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_34]), c_0_42])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 48
% 0.13/0.38  # Proof object clause steps            : 27
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 7
% 0.13/0.38  # Proof object clause conjectures      : 4
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 12
% 0.13/0.38  # Proof object simplifying inferences  : 6
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 33
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 33
% 0.13/0.38  # Processed clauses                    : 112
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 9
% 0.13/0.38  # ...remaining for further processing  : 103
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 105
% 0.13/0.38  # ...of the previous two non-trivial   : 89
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 103
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
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
% 0.13/0.38  # Current number of processed clauses  : 69
% 0.13/0.38  #    Positive orientable unit clauses  : 4
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 63
% 0.13/0.38  # Current number of unprocessed clauses: 42
% 0.13/0.38  # ...number of literals in the above   : 172
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 32
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 718
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 62
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 11
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5235
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.033 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.039 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
