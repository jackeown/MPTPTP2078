%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:41 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 (3299 expanded)
%              Number of clauses        :   61 (1220 expanded)
%              Number of leaves         :    9 ( 782 expanded)
%              Depth                    :   22
%              Number of atoms          :  264 (26464 expanded)
%              Number of equality atoms :   37 ( 855 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t107_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( ( v3_pre_topc(X4,X2)
                        & v4_tops_1(X4,X2) )
                     => v6_tops_1(X4,X2) )
                    & ( v6_tops_1(X3,X1)
                     => ( v3_pre_topc(X3,X1)
                        & v4_tops_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d8_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_tops_1(X2,X1)
          <=> X2 = k1_tops_1(X1,k2_pre_topc(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

fof(projectivity_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(d6_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
          <=> ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
              & r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( ( v3_pre_topc(X4,X2)
                          & v4_tops_1(X4,X2) )
                       => v6_tops_1(X4,X2) )
                      & ( v6_tops_1(X3,X1)
                       => ( v3_pre_topc(X3,X1)
                          & v4_tops_1(X3,X1) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t107_tops_1])).

fof(c_0_10,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | m1_subset_1(k2_pre_topc(X7,X8),k1_zfmisc_1(u1_struct_0(X7))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_11,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( v6_tops_1(esk3_0,esk1_0)
      | v3_pre_topc(esk4_0,esk2_0) )
    & ( ~ v3_pre_topc(esk3_0,esk1_0)
      | ~ v4_tops_1(esk3_0,esk1_0)
      | v3_pre_topc(esk4_0,esk2_0) )
    & ( v6_tops_1(esk3_0,esk1_0)
      | v4_tops_1(esk4_0,esk2_0) )
    & ( ~ v3_pre_topc(esk3_0,esk1_0)
      | ~ v4_tops_1(esk3_0,esk1_0)
      | v4_tops_1(esk4_0,esk2_0) )
    & ( v6_tops_1(esk3_0,esk1_0)
      | ~ v6_tops_1(esk4_0,esk2_0) )
    & ( ~ v3_pre_topc(esk3_0,esk1_0)
      | ~ v4_tops_1(esk3_0,esk1_0)
      | ~ v6_tops_1(esk4_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X13,X14] :
      ( ( ~ v6_tops_1(X14,X13)
        | X14 = k1_tops_1(X13,k2_pre_topc(X13,X14))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( X14 != k1_tops_1(X13,k2_pre_topc(X13,X14))
        | v6_tops_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_tops_1])])])])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | k1_tops_1(X15,k1_tops_1(X15,X16)) = k1_tops_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

cnf(c_0_14,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( X1 = k1_tops_1(X2,k2_pre_topc(X2,X1))
    | ~ v6_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(k1_tops_1(X11,k2_pre_topc(X11,X12)),X12)
        | ~ v4_tops_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( r1_tarski(X12,k2_pre_topc(X11,k1_tops_1(X11,X12)))
        | ~ v4_tops_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( ~ r1_tarski(k1_tops_1(X11,k2_pre_topc(X11,X12)),X12)
        | ~ r1_tarski(X12,k2_pre_topc(X11,k1_tops_1(X11,X12)))
        | v4_tops_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).

cnf(c_0_19,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_21,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0
    | ~ v6_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_15]),c_0_16])])).

cnf(c_0_22,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0)
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X21,X22,X23] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ v3_pre_topc(X22,X21)
      | ~ r1_tarski(X22,X23)
      | r1_tarski(X22,k1_tops_1(X21,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0)
    | v3_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_27,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | r1_tarski(X10,k2_pre_topc(X9,X10)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ v4_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))) = k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_16])])).

cnf(c_0_30,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_24]),c_0_25])])).

cnf(c_0_33,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0
    | v3_pre_topc(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)),esk4_0)
    | ~ v4_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_25])])).

cnf(c_0_37,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,k2_pre_topc(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25])])).

cnf(c_0_39,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | v3_pre_topc(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_24]),c_0_25])])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | r1_tarski(k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | r1_tarski(esk4_0,k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_24]),c_0_40])])).

cnf(c_0_44,plain,
    ( v6_tops_1(X1,X2)
    | X1 != k1_tops_1(X2,k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)) = esk4_0
    | k1_tops_1(esk1_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0)
    | ~ v6_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | v6_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_24]),c_0_25])])).

fof(c_0_48,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ v3_pre_topc(X20,X18)
        | k1_tops_1(X18,X20) = X20
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X18)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( k1_tops_1(X17,X19) != X19
        | v3_pre_topc(X19,X17)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X18)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_49,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | v6_tops_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( v3_pre_topc(X2,X1)
    | k1_tops_1(X1,X2) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk3_0)) = k1_tops_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_15]),c_0_16])])).

cnf(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_53,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0
    | k1_tops_1(esk1_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,esk3_0),esk1_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_16])])).

cnf(c_0_55,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_53])).

cnf(c_0_56,plain,
    ( v4_tops_1(X2,X1)
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_57,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_55]),c_0_15])])).

cnf(c_0_58,negated_conjecture,
    ( v4_tops_1(esk3_0,esk1_0)
    | ~ r1_tarski(esk3_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_15]),c_0_16])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_15]),c_0_16])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_61,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | ~ v3_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_62,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_24]),c_0_25])])).

cnf(c_0_63,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ v3_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_64,negated_conjecture,
    ( v4_tops_1(esk3_0,esk1_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_55]),c_0_59])])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_67,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_62])])).

cnf(c_0_68,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_33]),c_0_65])]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_30]),c_0_65])]),c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_68]),c_0_24]),c_0_40])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_69])])).

cnf(c_0_72,negated_conjecture,
    ( k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_70]),c_0_71])])).

cnf(c_0_73,negated_conjecture,
    ( v6_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_72]),c_0_24]),c_0_25])])).

cnf(c_0_74,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0)
    | ~ v6_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_75,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_73])])).

cnf(c_0_76,negated_conjecture,
    ( ~ v6_tops_1(esk4_0,esk2_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_62])])).

cnf(c_0_77,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_75])])).

cnf(c_0_78,negated_conjecture,
    ( ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_73])])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_77]),c_0_65])]),c_0_78]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:17:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.21/0.41  # and selection function SelectNewComplexAHP.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.042 s
% 0.21/0.41  # Presaturation interreduction done
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(t107_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((v3_pre_topc(X4,X2)&v4_tops_1(X4,X2))=>v6_tops_1(X4,X2))&(v6_tops_1(X3,X1)=>(v3_pre_topc(X3,X1)&v4_tops_1(X3,X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_tops_1)).
% 0.21/0.41  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.21/0.41  fof(d8_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_tops_1(X2,X1)<=>X2=k1_tops_1(X1,k2_pre_topc(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tops_1)).
% 0.21/0.41  fof(projectivity_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 0.21/0.41  fof(d6_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)<=>(r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)&r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 0.21/0.41  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 0.21/0.41  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.21/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.41  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 0.21/0.41  fof(c_0_9, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((v3_pre_topc(X4,X2)&v4_tops_1(X4,X2))=>v6_tops_1(X4,X2))&(v6_tops_1(X3,X1)=>(v3_pre_topc(X3,X1)&v4_tops_1(X3,X1))))))))), inference(assume_negation,[status(cth)],[t107_tops_1])).
% 0.21/0.41  fof(c_0_10, plain, ![X7, X8]:(~l1_pre_topc(X7)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|m1_subset_1(k2_pre_topc(X7,X8),k1_zfmisc_1(u1_struct_0(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.21/0.41  fof(c_0_11, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((((v6_tops_1(esk3_0,esk1_0)|v3_pre_topc(esk4_0,esk2_0))&(~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|v3_pre_topc(esk4_0,esk2_0)))&((v6_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0))&(~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0))))&((v6_tops_1(esk3_0,esk1_0)|~v6_tops_1(esk4_0,esk2_0))&(~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|~v6_tops_1(esk4_0,esk2_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.21/0.41  fof(c_0_12, plain, ![X13, X14]:((~v6_tops_1(X14,X13)|X14=k1_tops_1(X13,k2_pre_topc(X13,X14))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(X14!=k1_tops_1(X13,k2_pre_topc(X13,X14))|v6_tops_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_tops_1])])])])).
% 0.21/0.41  fof(c_0_13, plain, ![X15, X16]:(~l1_pre_topc(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|k1_tops_1(X15,k1_tops_1(X15,X16))=k1_tops_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).
% 0.21/0.41  cnf(c_0_14, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_17, plain, (X1=k1_tops_1(X2,k2_pre_topc(X2,X1))|~v6_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.41  fof(c_0_18, plain, ![X11, X12]:(((r1_tarski(k1_tops_1(X11,k2_pre_topc(X11,X12)),X12)|~v4_tops_1(X12,X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~l1_pre_topc(X11))&(r1_tarski(X12,k2_pre_topc(X11,k1_tops_1(X11,X12)))|~v4_tops_1(X12,X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~l1_pre_topc(X11)))&(~r1_tarski(k1_tops_1(X11,k2_pre_topc(X11,X12)),X12)|~r1_tarski(X12,k2_pre_topc(X11,k1_tops_1(X11,X12)))|v4_tops_1(X12,X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~l1_pre_topc(X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).
% 0.21/0.41  cnf(c_0_19, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.41  cnf(c_0_20, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.21/0.41  cnf(c_0_21, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0|~v6_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_15]), c_0_16])])).
% 0.21/0.41  cnf(c_0_22, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  fof(c_0_23, plain, ![X21, X22, X23]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~v3_pre_topc(X22,X21)|~r1_tarski(X22,X23)|r1_tarski(X22,k1_tops_1(X21,X23)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 0.21/0.41  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_26, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)|v3_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  fof(c_0_27, plain, ![X9, X10]:(~l1_pre_topc(X9)|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|r1_tarski(X10,k2_pre_topc(X9,X10)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.21/0.41  cnf(c_0_28, plain, (r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~v4_tops_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.41  cnf(c_0_29, negated_conjecture, (k1_tops_1(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)))=k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_16])])).
% 0.21/0.41  cnf(c_0_30, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0|v4_tops_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.41  cnf(c_0_31, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.41  cnf(c_0_32, negated_conjecture, (m1_subset_1(k2_pre_topc(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_24]), c_0_25])])).
% 0.21/0.41  cnf(c_0_33, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0|v3_pre_topc(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_21, c_0_26])).
% 0.21/0.41  cnf(c_0_34, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.41  fof(c_0_35, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.41  cnf(c_0_36, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)),esk4_0)|~v4_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_25])])).
% 0.21/0.41  cnf(c_0_37, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|v4_tops_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.41  cnf(c_0_38, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,k2_pre_topc(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_25])])).
% 0.21/0.41  cnf(c_0_39, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|v3_pre_topc(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_33])).
% 0.21/0.41  cnf(c_0_40, negated_conjecture, (r1_tarski(esk4_0,k2_pre_topc(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_24]), c_0_25])])).
% 0.21/0.41  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.41  cnf(c_0_42, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|r1_tarski(k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.41  cnf(c_0_43, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|r1_tarski(esk4_0,k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_24]), c_0_40])])).
% 0.21/0.41  cnf(c_0_44, plain, (v6_tops_1(X1,X2)|X1!=k1_tops_1(X2,k2_pre_topc(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.41  cnf(c_0_45, negated_conjecture, (k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))=esk4_0|k1_tops_1(esk1_0,esk3_0)=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.21/0.41  cnf(c_0_46, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)|~v6_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_47, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|v6_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_24]), c_0_25])])).
% 0.21/0.41  fof(c_0_48, plain, ![X17, X18, X19, X20]:((~v3_pre_topc(X20,X18)|k1_tops_1(X18,X20)=X20|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X18)|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(k1_tops_1(X17,X19)!=X19|v3_pre_topc(X19,X17)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X18)|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.21/0.41  cnf(c_0_49, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|v6_tops_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.21/0.41  cnf(c_0_50, plain, (v3_pre_topc(X2,X1)|k1_tops_1(X1,X2)!=X2|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.41  cnf(c_0_51, negated_conjecture, (k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk3_0))=k1_tops_1(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_15]), c_0_16])])).
% 0.21/0.41  cnf(c_0_52, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_53, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0|k1_tops_1(esk1_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_21, c_0_49])).
% 0.21/0.41  cnf(c_0_54, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,esk3_0),esk1_0)|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_16])])).
% 0.21/0.41  cnf(c_0_55, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_29, c_0_53])).
% 0.21/0.41  cnf(c_0_56, plain, (v4_tops_1(X2,X1)|~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.41  cnf(c_0_57, negated_conjecture, (v3_pre_topc(esk3_0,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_55]), c_0_15])])).
% 0.21/0.41  cnf(c_0_58, negated_conjecture, (v4_tops_1(esk3_0,esk1_0)|~r1_tarski(esk3_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)))|~r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_15]), c_0_16])])).
% 0.21/0.41  cnf(c_0_59, negated_conjecture, (r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_15]), c_0_16])])).
% 0.21/0.41  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.41  cnf(c_0_61, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_62, negated_conjecture, (v3_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_24]), c_0_25])])).
% 0.21/0.41  cnf(c_0_63, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_64, negated_conjecture, (v4_tops_1(esk3_0,esk1_0)|~r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_55]), c_0_59])])).
% 0.21/0.41  cnf(c_0_65, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 0.21/0.41  cnf(c_0_66, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.21/0.41  cnf(c_0_67, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_62])])).
% 0.21/0.41  cnf(c_0_68, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_33]), c_0_65])]), c_0_66])).
% 0.21/0.41  cnf(c_0_69, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_30]), c_0_65])]), c_0_67])).
% 0.21/0.41  cnf(c_0_70, negated_conjecture, (r1_tarski(esk4_0,k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_68]), c_0_24]), c_0_40])])).
% 0.21/0.41  cnf(c_0_71, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_69])])).
% 0.21/0.41  cnf(c_0_72, negated_conjecture, (k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_70]), c_0_71])])).
% 0.21/0.41  cnf(c_0_73, negated_conjecture, (v6_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_72]), c_0_24]), c_0_25])])).
% 0.21/0.41  cnf(c_0_74, negated_conjecture, (~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|~v6_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_75, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_73])])).
% 0.21/0.41  cnf(c_0_76, negated_conjecture, (~v6_tops_1(esk4_0,esk2_0)|~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_62])])).
% 0.21/0.41  cnf(c_0_77, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_75])])).
% 0.21/0.41  cnf(c_0_78, negated_conjecture, (~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_73])])).
% 0.21/0.41  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_77]), c_0_65])]), c_0_78]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 80
% 0.21/0.41  # Proof object clause steps            : 61
% 0.21/0.41  # Proof object formula steps           : 19
% 0.21/0.41  # Proof object conjectures             : 52
% 0.21/0.41  # Proof object clause conjectures      : 49
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 22
% 0.21/0.41  # Proof object initial formulas used   : 9
% 0.21/0.41  # Proof object generating inferences   : 28
% 0.21/0.41  # Proof object simplifying inferences  : 72
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 9
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 25
% 0.21/0.41  # Removed in clause preprocessing      : 0
% 0.21/0.41  # Initial clauses in saturation        : 25
% 0.21/0.41  # Processed clauses                    : 141
% 0.21/0.41  # ...of these trivial                  : 3
% 0.21/0.41  # ...subsumed                          : 10
% 0.21/0.41  # ...remaining for further processing  : 128
% 0.21/0.41  # Other redundant clauses eliminated   : 2
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 1
% 0.21/0.41  # Backward-rewritten                   : 55
% 0.21/0.41  # Generated clauses                    : 144
% 0.21/0.41  # ...of the previous two non-trivial   : 151
% 0.21/0.41  # Contextual simplify-reflections      : 3
% 0.21/0.41  # Paramodulations                      : 142
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 2
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 46
% 0.21/0.41  #    Positive orientable unit clauses  : 25
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 1
% 0.21/0.41  #    Non-unit-clauses                  : 20
% 0.21/0.41  # Current number of unprocessed clauses: 47
% 0.21/0.41  # ...number of literals in the above   : 113
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 80
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 458
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 275
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 14
% 0.21/0.41  # Unit Clause-clause subsumption calls : 69
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 19
% 0.21/0.41  # BW rewrite match successes           : 9
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 5507
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.055 s
% 0.21/0.41  # System time              : 0.006 s
% 0.21/0.41  # Total time               : 0.061 s
% 0.21/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
