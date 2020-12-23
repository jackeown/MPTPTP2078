%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:21 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 177 expanded)
%              Number of clauses        :   28 (  57 expanded)
%              Number of leaves         :    7 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  203 (1167 expanded)
%              Number of equality atoms :   18 ( 112 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_pre_topc(X3,k8_tmap_1(X1,X2))
             => ( u1_struct_0(X3) = u1_struct_0(X2)
               => ( v1_tsep_1(X3,k8_tmap_1(X1,X2))
                  & m1_pre_topc(X3,k8_tmap_1(X1,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_tmap_1)).

fof(t16_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(t114_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
            & ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

fof(t102_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r2_hidden(X2,k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_pre_topc(X3,k8_tmap_1(X1,X2))
               => ( u1_struct_0(X3) = u1_struct_0(X2)
                 => ( v1_tsep_1(X3,k8_tmap_1(X1,X2))
                    & m1_pre_topc(X3,k8_tmap_1(X1,X2)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_tmap_1])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & m1_pre_topc(esk3_0,k8_tmap_1(esk1_0,esk2_0))
    & u1_struct_0(esk3_0) = u1_struct_0(esk2_0)
    & ( ~ v1_tsep_1(esk3_0,k8_tmap_1(esk1_0,esk2_0))
      | ~ m1_pre_topc(esk3_0,k8_tmap_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_9,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v1_tsep_1(X14,X13)
        | ~ m1_pre_topc(X14,X13)
        | v3_pre_topc(X15,X13)
        | X15 != u1_struct_0(X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_pre_topc(X14,X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( v1_tsep_1(X14,X13)
        | ~ v3_pre_topc(X15,X13)
        | X15 != u1_struct_0(X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_pre_topc(X14,X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_pre_topc(X14,X13)
        | ~ v3_pre_topc(X15,X13)
        | X15 != u1_struct_0(X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_pre_topc(X14,X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_10,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X16)
      | m1_subset_1(u1_struct_0(X17),k1_zfmisc_1(u1_struct_0(X16))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_11,negated_conjecture,
    ( ~ v1_tsep_1(esk3_0,k8_tmap_1(esk1_0,esk2_0))
    | ~ m1_pre_topc(esk3_0,k8_tmap_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_pre_topc(esk3_0,k8_tmap_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_tsep_1(esk3_0,k8_tmap_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12])])).

cnf(c_0_16,plain,
    ( v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_18,plain,(
    ! [X6,X7] :
      ( ( v1_pre_topc(k8_tmap_1(X6,X7))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(X7,X6) )
      & ( v2_pre_topc(k8_tmap_1(X6,X7))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(X7,X6) )
      & ( l1_pre_topc(k8_tmap_1(X6,X7))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(X7,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_pre_topc(k8_tmap_1(esk1_0,esk2_0))
    | ~ v3_pre_topc(u1_struct_0(esk2_0),k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_pre_topc(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_12]),c_0_17])])).

cnf(c_0_20,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_25,plain,(
    ! [X4,X5] :
      ( ( ~ v3_pre_topc(X5,X4)
        | r2_hidden(X5,u1_pre_topc(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
      & ( ~ r2_hidden(X5,u1_pre_topc(X4))
        | v3_pre_topc(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(k8_tmap_1(esk1_0,esk2_0))))
    | ~ l1_pre_topc(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_12]),c_0_17])).

cnf(c_0_27,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk2_0),k8_tmap_1(esk1_0,esk2_0))
    | ~ l1_pre_topc(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_29,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(k8_tmap_1(esk1_0,esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk2_0),k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

fof(c_0_32,plain,(
    ! [X10,X11,X12] :
      ( ( u1_struct_0(k8_tmap_1(X10,X11)) = u1_struct_0(X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | X12 != u1_struct_0(X11)
        | u1_pre_topc(k8_tmap_1(X10,X11)) = k5_tmap_1(X10,X12)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

fof(c_0_33,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
      | r2_hidden(X9,k5_tmap_1(X8,X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t102_tmap_1])])])])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(k8_tmap_1(esk1_0,esk2_0)))
    | ~ l1_pre_topc(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_35,plain,
    ( u1_pre_topc(k8_tmap_1(X2,X3)) = k5_tmap_1(X2,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != u1_struct_0(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_21]),c_0_23])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(k8_tmap_1(esk1_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_27]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_39,plain,
    ( u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk2_0),k5_tmap_1(esk1_0,u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.029 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t115_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_pre_topc(X3,k8_tmap_1(X1,X2))=>(u1_struct_0(X3)=u1_struct_0(X2)=>(v1_tsep_1(X3,k8_tmap_1(X1,X2))&m1_pre_topc(X3,k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_tmap_1)).
% 0.13/0.37  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.13/0.37  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.13/0.37  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.13/0.37  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.13/0.37  fof(t114_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 0.13/0.37  fof(t102_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r2_hidden(X2,k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_tmap_1)).
% 0.13/0.37  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_pre_topc(X3,k8_tmap_1(X1,X2))=>(u1_struct_0(X3)=u1_struct_0(X2)=>(v1_tsep_1(X3,k8_tmap_1(X1,X2))&m1_pre_topc(X3,k8_tmap_1(X1,X2)))))))), inference(assume_negation,[status(cth)],[t115_tmap_1])).
% 0.13/0.37  fof(c_0_8, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&(m1_pre_topc(esk3_0,k8_tmap_1(esk1_0,esk2_0))&(u1_struct_0(esk3_0)=u1_struct_0(esk2_0)&(~v1_tsep_1(esk3_0,k8_tmap_1(esk1_0,esk2_0))|~m1_pre_topc(esk3_0,k8_tmap_1(esk1_0,esk2_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.13/0.37  fof(c_0_9, plain, ![X13, X14, X15]:((~v1_tsep_1(X14,X13)|~m1_pre_topc(X14,X13)|v3_pre_topc(X15,X13)|X15!=u1_struct_0(X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))|~m1_pre_topc(X14,X13)|(~v2_pre_topc(X13)|~l1_pre_topc(X13)))&((v1_tsep_1(X14,X13)|~v3_pre_topc(X15,X13)|X15!=u1_struct_0(X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))|~m1_pre_topc(X14,X13)|(~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(m1_pre_topc(X14,X13)|~v3_pre_topc(X15,X13)|X15!=u1_struct_0(X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))|~m1_pre_topc(X14,X13)|(~v2_pre_topc(X13)|~l1_pre_topc(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.13/0.37  fof(c_0_10, plain, ![X16, X17]:(~l1_pre_topc(X16)|(~m1_pre_topc(X17,X16)|m1_subset_1(u1_struct_0(X17),k1_zfmisc_1(u1_struct_0(X16))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (~v1_tsep_1(esk3_0,k8_tmap_1(esk1_0,esk2_0))|~m1_pre_topc(esk3_0,k8_tmap_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (m1_pre_topc(esk3_0,k8_tmap_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_13, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_14, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (~v1_tsep_1(esk3_0,k8_tmap_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12])])).
% 0.13/0.37  cnf(c_0_16, plain, (v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_14])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  fof(c_0_18, plain, ![X6, X7]:(((v1_pre_topc(k8_tmap_1(X6,X7))|(v2_struct_0(X6)|~v2_pre_topc(X6)|~l1_pre_topc(X6)|~m1_pre_topc(X7,X6)))&(v2_pre_topc(k8_tmap_1(X6,X7))|(v2_struct_0(X6)|~v2_pre_topc(X6)|~l1_pre_topc(X6)|~m1_pre_topc(X7,X6))))&(l1_pre_topc(k8_tmap_1(X6,X7))|(v2_struct_0(X6)|~v2_pre_topc(X6)|~l1_pre_topc(X6)|~m1_pre_topc(X7,X6)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (~v2_pre_topc(k8_tmap_1(esk1_0,esk2_0))|~v3_pre_topc(u1_struct_0(esk2_0),k8_tmap_1(esk1_0,esk2_0))|~l1_pre_topc(k8_tmap_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_12]), c_0_17])])).
% 0.13/0.37  cnf(c_0_20, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  fof(c_0_25, plain, ![X4, X5]:((~v3_pre_topc(X5,X4)|r2_hidden(X5,u1_pre_topc(X4))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))&(~r2_hidden(X5,u1_pre_topc(X4))|v3_pre_topc(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(k8_tmap_1(esk1_0,esk2_0))))|~l1_pre_topc(k8_tmap_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_12]), c_0_17])).
% 0.13/0.37  cnf(c_0_27, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk2_0),k8_tmap_1(esk1_0,esk2_0))|~l1_pre_topc(k8_tmap_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.13/0.37  cnf(c_0_29, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(k8_tmap_1(esk1_0,esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk2_0),k8_tmap_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_27]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.13/0.37  fof(c_0_32, plain, ![X10, X11, X12]:((u1_struct_0(k8_tmap_1(X10,X11))=u1_struct_0(X10)|(v2_struct_0(X11)|~m1_pre_topc(X11,X10))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))|(X12!=u1_struct_0(X11)|u1_pre_topc(k8_tmap_1(X10,X11))=k5_tmap_1(X10,X12))|(v2_struct_0(X11)|~m1_pre_topc(X11,X10))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).
% 0.13/0.37  fof(c_0_33, plain, ![X8, X9]:(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)|(~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|r2_hidden(X9,k5_tmap_1(X8,X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t102_tmap_1])])])])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (~r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(k8_tmap_1(esk1_0,esk2_0)))|~l1_pre_topc(k8_tmap_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.13/0.37  cnf(c_0_35, plain, (u1_pre_topc(k8_tmap_1(X2,X3))=k5_tmap_1(X2,X1)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X1!=u1_struct_0(X3)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_36, plain, (v2_struct_0(X1)|r2_hidden(X2,k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_21]), c_0_23])])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (~r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(k8_tmap_1(esk1_0,esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_27]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.13/0.37  cnf(c_0_39, plain, (u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]), c_0_14])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (r2_hidden(u1_struct_0(esk2_0),k5_tmap_1(esk1_0,u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_22]), c_0_23])]), c_0_24])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_21]), c_0_22]), c_0_23])]), c_0_24]), c_0_41]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 43
% 0.13/0.37  # Proof object clause steps            : 28
% 0.13/0.37  # Proof object formula steps           : 15
% 0.13/0.37  # Proof object conjectures             : 22
% 0.13/0.37  # Proof object clause conjectures      : 19
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 15
% 0.13/0.37  # Proof object initial formulas used   : 7
% 0.13/0.37  # Proof object generating inferences   : 10
% 0.13/0.37  # Proof object simplifying inferences  : 44
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 7
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 20
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 19
% 0.13/0.37  # Processed clauses                    : 56
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 56
% 0.13/0.37  # Other redundant clauses eliminated   : 3
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 1
% 0.13/0.37  # Generated clauses                    : 28
% 0.13/0.37  # ...of the previous two non-trivial   : 23
% 0.13/0.37  # Contextual simplify-reflections      : 4
% 0.13/0.37  # Paramodulations                      : 25
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 3
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 32
% 0.13/0.37  #    Positive orientable unit clauses  : 8
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 5
% 0.13/0.37  #    Non-unit-clauses                  : 19
% 0.13/0.37  # Current number of unprocessed clauses: 5
% 0.13/0.37  # ...number of literals in the above   : 35
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 21
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 249
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 18
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.37  # Unit Clause-clause subsumption calls : 6
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 2
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2568
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.030 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.035 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
