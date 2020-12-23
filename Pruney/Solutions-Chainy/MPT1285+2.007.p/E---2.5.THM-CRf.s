%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:40 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 (10440 expanded)
%              Number of clauses        :   80 (3829 expanded)
%              Number of leaves         :   10 (2426 expanded)
%              Depth                    :   29
%              Number of atoms          :  308 (89636 expanded)
%              Number of equality atoms :   47 (2455 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d8_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_tops_1(X2,X1)
          <=> X2 = k1_tops_1(X1,k2_pre_topc(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(d6_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
          <=> ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
              & r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(projectivity_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | m1_subset_1(k2_pre_topc(X7,X8),k1_zfmisc_1(u1_struct_0(X7))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_12,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X11,X12] :
      ( ( ~ v6_tops_1(X12,X11)
        | X12 = k1_tops_1(X11,k2_pre_topc(X11,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( X12 != k1_tops_1(X11,k2_pre_topc(X11,X12))
        | v6_tops_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_tops_1])])])])).

fof(c_0_14,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ v3_pre_topc(X25,X23)
        | k1_tops_1(X23,X25) = X25
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X23)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( k1_tops_1(X22,X24) != X24
        | v3_pre_topc(X24,X22)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X23)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | v3_pre_topc(k1_tops_1(X13,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = k1_tops_1(X2,k2_pre_topc(X2,X1))
    | ~ v6_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0
    | ~ v6_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_17]),c_0_18])])).

cnf(c_0_25,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0)
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0)
    | v3_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_27,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(k1_tops_1(X9,k2_pre_topc(X9,X10)),X10)
        | ~ v4_tops_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( r1_tarski(X10,k2_pre_topc(X9,k1_tops_1(X9,X10)))
        | ~ v4_tops_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( ~ r1_tarski(k1_tops_1(X9,k2_pre_topc(X9,X10)),X10)
        | ~ r1_tarski(X10,k2_pre_topc(X9,k1_tops_1(X9,X10)))
        | v4_tops_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).

cnf(c_0_28,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_21]),c_0_18])])).

cnf(c_0_29,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_21]),c_0_18])])).

cnf(c_0_30,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0
    | v3_pre_topc(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_26])).

fof(c_0_34,plain,(
    ! [X19,X20,X21] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ r1_tarski(X20,X21)
      | r1_tarski(k1_tops_1(X19,X20),k1_tops_1(X19,X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))
    | ~ v4_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | ~ v3_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_18])])).

cnf(c_0_37,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0)
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k1_tops_1(esk2_0,esk4_0) = esk4_0
    | ~ v3_pre_topc(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_31]),c_0_32])])).

cnf(c_0_39,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | v3_pre_topc(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_31]),c_0_32])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)))
    | ~ v4_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_31]),c_0_32])])).

cnf(c_0_43,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k1_tops_1(esk2_0,esk4_0) = esk4_0
    | v3_pre_topc(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ v4_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,k2_pre_topc(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_32])])).

cnf(c_0_47,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k1_tops_1(esk2_0,esk4_0) = esk4_0
    | k1_tops_1(esk1_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_44])).

fof(c_0_49,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)),esk4_0)
    | ~ v4_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_31]),c_0_32])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk4_0),k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)))
    | ~ r1_tarski(esk4_0,k2_pre_topc(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | r1_tarski(esk4_0,k2_pre_topc(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | r1_tarski(k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | r1_tarski(k1_tops_1(esk2_0,esk4_0),k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)) = esk4_0
    | k1_tops_1(esk1_0,esk3_0) = esk3_0
    | ~ r1_tarski(esk4_0,k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | r1_tarski(esk4_0,k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_48])).

cnf(c_0_58,plain,
    ( v6_tops_1(X1,X2)
    | X1 != k1_tops_1(X2,k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)) = esk4_0
    | k1_tops_1(esk1_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_60,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | k1_tops_1(X15,k1_tops_1(X15,X16)) = k1_tops_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

cnf(c_0_61,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0)
    | ~ v6_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_62,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | v6_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_31]),c_0_32])])).

cnf(c_0_63,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | v6_tops_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_65,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | r1_tarski(k1_tops_1(X17,X18),X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_66,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))) = k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_23]),c_0_18])])).

cnf(c_0_67,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0
    | k1_tops_1(esk1_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_64])).

cnf(c_0_68,plain,
    ( v4_tops_1(X2,X1)
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_21]),c_0_18])])).

cnf(c_0_71,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( v4_tops_1(esk3_0,esk1_0)
    | ~ r1_tarski(esk3_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_17]),c_0_18])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),k2_pre_topc(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_23]),c_0_18])])).

cnf(c_0_74,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | ~ v3_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_75,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ v3_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_77,negated_conjecture,
    ( v4_tops_1(esk3_0,esk1_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0)
    | ~ r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_33])).

cnf(c_0_79,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_81,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_30])).

cnf(c_0_82,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_37])).

cnf(c_0_83,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_81]),c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_33]),c_0_84])])).

cnf(c_0_87,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_30]),c_0_84])])).

cnf(c_0_88,negated_conjecture,
    ( k1_tops_1(esk2_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_86])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_87])]),c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_88]),c_0_89])])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_87])])).

cnf(c_0_92,negated_conjecture,
    ( k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_90]),c_0_91])])).

cnf(c_0_93,negated_conjecture,
    ( v6_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_92]),c_0_31]),c_0_32])])).

cnf(c_0_94,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0)
    | ~ v6_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_95,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_93])])).

cnf(c_0_96,negated_conjecture,
    ( ~ v6_tops_1(esk4_0,esk2_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_75])])).

cnf(c_0_97,negated_conjecture,
    ( k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_95])])).

cnf(c_0_98,negated_conjecture,
    ( ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_93])])).

cnf(c_0_99,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_97]),c_0_84])]),c_0_98])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_97]),c_0_99]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 17:48:20 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.20/0.39  # and selection function SelectNewComplexAHP.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.019 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t107_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((v3_pre_topc(X4,X2)&v4_tops_1(X4,X2))=>v6_tops_1(X4,X2))&(v6_tops_1(X3,X1)=>(v3_pre_topc(X3,X1)&v4_tops_1(X3,X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 0.20/0.39  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.20/0.39  fof(d8_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_tops_1(X2,X1)<=>X2=k1_tops_1(X1,k2_pre_topc(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 0.20/0.39  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 0.20/0.39  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.20/0.39  fof(d6_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)<=>(r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)&r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 0.20/0.39  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(projectivity_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 0.20/0.39  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.20/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((v3_pre_topc(X4,X2)&v4_tops_1(X4,X2))=>v6_tops_1(X4,X2))&(v6_tops_1(X3,X1)=>(v3_pre_topc(X3,X1)&v4_tops_1(X3,X1))))))))), inference(assume_negation,[status(cth)],[t107_tops_1])).
% 0.20/0.39  fof(c_0_11, plain, ![X7, X8]:(~l1_pre_topc(X7)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|m1_subset_1(k2_pre_topc(X7,X8),k1_zfmisc_1(u1_struct_0(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.20/0.39  fof(c_0_12, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((((v6_tops_1(esk3_0,esk1_0)|v3_pre_topc(esk4_0,esk2_0))&(~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|v3_pre_topc(esk4_0,esk2_0)))&((v6_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0))&(~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0))))&((v6_tops_1(esk3_0,esk1_0)|~v6_tops_1(esk4_0,esk2_0))&(~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|~v6_tops_1(esk4_0,esk2_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.20/0.39  fof(c_0_13, plain, ![X11, X12]:((~v6_tops_1(X12,X11)|X12=k1_tops_1(X11,k2_pre_topc(X11,X12))|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~l1_pre_topc(X11))&(X12!=k1_tops_1(X11,k2_pre_topc(X11,X12))|v6_tops_1(X12,X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|~l1_pre_topc(X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_tops_1])])])])).
% 0.20/0.39  fof(c_0_14, plain, ![X22, X23, X24, X25]:((~v3_pre_topc(X25,X23)|k1_tops_1(X23,X25)=X25|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X23)|(~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(k1_tops_1(X22,X24)!=X24|v3_pre_topc(X24,X22)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X23)|(~v2_pre_topc(X22)|~l1_pre_topc(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.20/0.39  fof(c_0_15, plain, ![X13, X14]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|v3_pre_topc(k1_tops_1(X13,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.20/0.39  cnf(c_0_16, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_19, plain, (X1=k1_tops_1(X2,k2_pre_topc(X2,X1))|~v6_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_20, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_22, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0|~v6_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_17]), c_0_18])])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)|v3_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  fof(c_0_27, plain, ![X9, X10]:(((r1_tarski(k1_tops_1(X9,k2_pre_topc(X9,X10)),X10)|~v4_tops_1(X10,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))&(r1_tarski(X10,k2_pre_topc(X9,k1_tops_1(X9,X10)))|~v4_tops_1(X10,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9)))&(~r1_tarski(k1_tops_1(X9,k2_pre_topc(X9,X10)),X10)|~r1_tarski(X10,k2_pre_topc(X9,k1_tops_1(X9,X10)))|v4_tops_1(X10,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_21]), c_0_18])])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_21]), c_0_18])])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0|v4_tops_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0|v3_pre_topc(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_26])).
% 0.20/0.39  fof(c_0_34, plain, ![X19, X20, X21]:(~l1_pre_topc(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(~r1_tarski(X20,X21)|r1_tarski(k1_tops_1(X19,X20),k1_tops_1(X19,X21)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.20/0.39  cnf(c_0_35, plain, (r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))|~v4_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|~v3_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_17]), c_0_18])])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (v3_pre_topc(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (k1_tops_1(esk2_0,esk4_0)=esk4_0|~v3_pre_topc(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_31]), c_0_32])])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|v3_pre_topc(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_29, c_0_33])).
% 0.20/0.39  cnf(c_0_40, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (m1_subset_1(k2_pre_topc(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_31]), c_0_32])])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)))|~v4_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_31]), c_0_32])])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|v4_tops_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (k1_tops_1(esk2_0,esk4_0)=esk4_0|v3_pre_topc(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.39  cnf(c_0_45, plain, (r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~v4_tops_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,k2_pre_topc(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_32])])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (k1_tops_1(esk2_0,esk4_0)=esk4_0|k1_tops_1(esk1_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_36, c_0_44])).
% 0.20/0.39  fof(c_0_49, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)),esk4_0)|~v4_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_31]), c_0_32])])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk4_0),k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)))|~r1_tarski(esk4_0,k2_pre_topc(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_31])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|r1_tarski(esk4_0,k2_pre_topc(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.39  cnf(c_0_53, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|r1_tarski(k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_43])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|r1_tarski(k1_tops_1(esk2_0,esk4_0),k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))=esk4_0|k1_tops_1(esk1_0,esk3_0)=esk3_0|~r1_tarski(esk4_0,k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|r1_tarski(esk4_0,k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_55, c_0_48])).
% 0.20/0.39  cnf(c_0_58, plain, (v6_tops_1(X1,X2)|X1!=k1_tops_1(X2,k2_pre_topc(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))=esk4_0|k1_tops_1(esk1_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.39  fof(c_0_60, plain, ![X15, X16]:(~l1_pre_topc(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|k1_tops_1(X15,k1_tops_1(X15,X16))=k1_tops_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)|~v6_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|v6_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_31]), c_0_32])])).
% 0.20/0.39  cnf(c_0_63, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0|v6_tops_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.39  fof(c_0_65, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|r1_tarski(k1_tops_1(X17,X18),X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (k1_tops_1(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)))=k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_23]), c_0_18])])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0|k1_tops_1(esk1_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_24, c_0_64])).
% 0.20/0.39  cnf(c_0_68, plain, (v4_tops_1(X2,X1)|~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_69, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_21]), c_0_18])])).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, (k1_tops_1(esk1_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (v4_tops_1(esk3_0,esk1_0)|~r1_tarski(esk3_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)))|~r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_17]), c_0_18])])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),k2_pre_topc(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_23]), c_0_18])])).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (v3_pre_topc(esk3_0,esk1_0)), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_77, negated_conjecture, (v4_tops_1(esk3_0,esk1_0)|~r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0)|~r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0))), inference(rw,[status(thm)],[c_0_72, c_0_71])).
% 0.20/0.39  cnf(c_0_78, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_73, c_0_33])).
% 0.20/0.39  cnf(c_0_79, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75])])).
% 0.20/0.39  cnf(c_0_80, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.39  cnf(c_0_81, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_73, c_0_30])).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|~v4_tops_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_76, c_0_37])).
% 0.20/0.39  cnf(c_0_83, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|~r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.20/0.39  cnf(c_0_84, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_80])).
% 0.20/0.39  cnf(c_0_85, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|~r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_81]), c_0_82])).
% 0.20/0.39  cnf(c_0_86, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_33]), c_0_84])])).
% 0.20/0.39  cnf(c_0_87, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_30]), c_0_84])])).
% 0.20/0.39  cnf(c_0_88, negated_conjecture, (k1_tops_1(esk2_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_86])])).
% 0.20/0.39  cnf(c_0_89, negated_conjecture, (r1_tarski(esk4_0,k2_pre_topc(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_87])]), c_0_88])).
% 0.20/0.39  cnf(c_0_90, negated_conjecture, (r1_tarski(esk4_0,k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_88]), c_0_89])])).
% 0.20/0.39  cnf(c_0_91, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_87])])).
% 0.20/0.39  cnf(c_0_92, negated_conjecture, (k1_tops_1(esk2_0,k2_pre_topc(esk2_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_90]), c_0_91])])).
% 0.20/0.39  cnf(c_0_93, negated_conjecture, (v6_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_92]), c_0_31]), c_0_32])])).
% 0.20/0.39  cnf(c_0_94, negated_conjecture, (~v3_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|~v6_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_95, negated_conjecture, (v6_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_93])])).
% 0.20/0.39  cnf(c_0_96, negated_conjecture, (~v6_tops_1(esk4_0,esk2_0)|~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_75])])).
% 0.20/0.39  cnf(c_0_97, negated_conjecture, (k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_95])])).
% 0.20/0.39  cnf(c_0_98, negated_conjecture, (~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_93])])).
% 0.20/0.39  cnf(c_0_99, negated_conjecture, (~r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_97]), c_0_84])]), c_0_98])).
% 0.20/0.39  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_97]), c_0_99]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 101
% 0.20/0.39  # Proof object clause steps            : 80
% 0.20/0.39  # Proof object formula steps           : 21
% 0.20/0.39  # Proof object conjectures             : 69
% 0.20/0.39  # Proof object clause conjectures      : 66
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 24
% 0.20/0.39  # Proof object initial formulas used   : 10
% 0.20/0.39  # Proof object generating inferences   : 42
% 0.20/0.39  # Proof object simplifying inferences  : 74
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 10
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 26
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 26
% 0.20/0.39  # Processed clauses                    : 192
% 0.20/0.39  # ...of these trivial                  : 3
% 0.20/0.39  # ...subsumed                          : 17
% 0.20/0.39  # ...remaining for further processing  : 171
% 0.20/0.39  # Other redundant clauses eliminated   : 2
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 9
% 0.20/0.39  # Backward-rewritten                   : 78
% 0.20/0.39  # Generated clauses                    : 222
% 0.20/0.39  # ...of the previous two non-trivial   : 225
% 0.20/0.39  # Contextual simplify-reflections      : 2
% 0.20/0.39  # Paramodulations                      : 220
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 2
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 57
% 0.20/0.39  #    Positive orientable unit clauses  : 28
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 27
% 0.20/0.39  # Current number of unprocessed clauses: 76
% 0.20/0.39  # ...number of literals in the above   : 178
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 112
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 903
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 563
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 26
% 0.20/0.39  # Unit Clause-clause subsumption calls : 114
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 27
% 0.20/0.39  # BW rewrite match successes           : 9
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 7283
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.027 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.031 s
% 0.20/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
