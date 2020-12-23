%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:10 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 564 expanded)
%              Number of clauses        :   54 ( 211 expanded)
%              Number of leaves         :   13 ( 137 expanded)
%              Depth                    :   12
%              Number of atoms          :  263 (3424 expanded)
%              Number of equality atoms :   40 ( 434 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t86_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X1) )
                 => X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_14,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tops_1(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X1) )
                   => X3 = k1_xboole_0 ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_tops_1])).

fof(c_0_16,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | ~ r1_tarski(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_17,plain,(
    ! [X5] :
      ( X5 = k1_xboole_0
      | r2_hidden(esk1_1(X5),X5) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | r1_tarski(k1_tops_1(X21,X22),X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_21,plain,(
    ! [X11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_22,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ v3_pre_topc(X29,X27)
        | k1_tops_1(X27,X29) = X29
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( k1_tops_1(X26,X28) != X28
        | v3_pre_topc(X28,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

fof(c_0_23,negated_conjecture,(
    ! [X38] :
      ( v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ v2_tops_1(esk3_0,esk2_0) )
      & ( r1_tarski(esk4_0,esk3_0)
        | ~ v2_tops_1(esk3_0,esk2_0) )
      & ( v3_pre_topc(esk4_0,esk2_0)
        | ~ v2_tops_1(esk3_0,esk2_0) )
      & ( esk4_0 != k1_xboole_0
        | ~ v2_tops_1(esk3_0,esk2_0) )
      & ( v2_tops_1(esk3_0,esk2_0)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ r1_tarski(X38,esk3_0)
        | ~ v3_pre_topc(X38,esk2_0)
        | X38 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X19,X20] :
      ( ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | v3_pre_topc(k1_tops_1(X19,X20),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_30,plain,(
    ! [X33,X34] :
      ( ( ~ v2_tops_1(X34,X33)
        | k1_tops_1(X33,X34) = k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_pre_topc(X33) )
      & ( k1_tops_1(X33,X34) != k1_xboole_0
        | v2_tops_1(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

fof(c_0_31,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_32,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_36,plain,(
    ! [X23,X24,X25] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ r1_tarski(X24,X25)
      | r1_tarski(k1_tops_1(X23,X24),k1_tops_1(X23,X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,esk1_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_tops_1(X1,k1_xboole_0),X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_39,negated_conjecture,
    ( v2_tops_1(esk3_0,esk2_0)
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0)
    | ~ v3_pre_topc(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v2_tops_1(esk3_0,esk2_0)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_45,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,plain,
    ( v2_tops_1(X2,X1)
    | k1_tops_1(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( k1_tops_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k1_tops_1(esk2_0,X1) = k1_xboole_0
    | v2_tops_1(esk3_0,esk2_0)
    | ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_34]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = k1_xboole_0
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_34])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( k1_tops_1(esk2_0,esk4_0) = esk4_0
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_33]),c_0_34])]),c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( v2_tops_1(esk3_0,esk2_0)
    | k1_tops_1(esk2_0,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_42]),c_0_34])])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_xboole_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_28])])).

cnf(c_0_55,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = k1_xboole_0
    | ~ m1_subset_1(k1_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_42]),c_0_50])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k1_tops_1(esk2_0,esk4_0) = esk4_0
    | k1_tops_1(esk2_0,esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = k1_xboole_0
    | ~ r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | k1_tops_1(esk2_0,esk3_0) != k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_58]),c_0_34]),c_0_35])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_63,plain,
    ( k1_tops_1(X1,X2) = k1_xboole_0
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_65,plain,(
    ! [X30,X31,X32] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
      | ~ v3_pre_topc(X31,X30)
      | ~ r1_tarski(X31,X32)
      | r1_tarski(X31,k1_tops_1(X30,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_66,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_27]),c_0_34]),c_0_42])])).

cnf(c_0_67,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | k1_tops_1(esk2_0,esk3_0) != k1_xboole_0
    | ~ r1_tarski(esk4_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | k1_tops_1(esk2_0,esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_53])).

cnf(c_0_69,plain,
    ( k1_tops_1(X1,X2) = k1_xboole_0
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_56]),c_0_26])).

cnf(c_0_70,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) != k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_53])).

cnf(c_0_71,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( v2_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_66])])).

cnf(c_0_73,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | k1_tops_1(esk2_0,esk3_0) != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_57]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) != k1_xboole_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_58]),c_0_34])]),c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_66]),c_0_34]),c_0_42])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_72])])).

cnf(c_0_77,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_66])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_66])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_66])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_78])]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:17:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.18/0.38  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.028 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.18/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.38  fof(t86_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 0.18/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.18/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.18/0.38  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.18/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.18/0.38  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 0.18/0.38  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.18/0.38  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 0.18/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.38  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.18/0.38  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 0.18/0.38  fof(c_0_13, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.18/0.38  fof(c_0_14, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.38  fof(c_0_15, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t86_tops_1])).
% 0.18/0.38  fof(c_0_16, plain, ![X17, X18]:(~r2_hidden(X17,X18)|~r1_tarski(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.18/0.38  fof(c_0_17, plain, ![X5]:(X5=k1_xboole_0|r2_hidden(esk1_1(X5),X5)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.18/0.38  cnf(c_0_18, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.38  cnf(c_0_19, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.38  fof(c_0_20, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|r1_tarski(k1_tops_1(X21,X22),X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.18/0.38  fof(c_0_21, plain, ![X11]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.18/0.38  fof(c_0_22, plain, ![X26, X27, X28, X29]:((~v3_pre_topc(X29,X27)|k1_tops_1(X27,X29)=X29|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X27)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(k1_tops_1(X26,X28)!=X28|v3_pre_topc(X28,X26)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X27)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.18/0.38  fof(c_0_23, negated_conjecture, ![X38]:((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v2_tops_1(esk3_0,esk2_0))&(((r1_tarski(esk4_0,esk3_0)|~v2_tops_1(esk3_0,esk2_0))&(v3_pre_topc(esk4_0,esk2_0)|~v2_tops_1(esk3_0,esk2_0)))&(esk4_0!=k1_xboole_0|~v2_tops_1(esk3_0,esk2_0))))&(v2_tops_1(esk3_0,esk2_0)|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(esk2_0)))|(~r1_tarski(X38,esk3_0)|~v3_pre_topc(X38,esk2_0)|X38=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).
% 0.18/0.38  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.38  cnf(c_0_25, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.38  cnf(c_0_27, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.38  cnf(c_0_28, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.38  fof(c_0_29, plain, ![X19, X20]:(~v2_pre_topc(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|v3_pre_topc(k1_tops_1(X19,X20),X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.18/0.38  fof(c_0_30, plain, ![X33, X34]:((~v2_tops_1(X34,X33)|k1_tops_1(X33,X34)=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_pre_topc(X33))&(k1_tops_1(X33,X34)!=k1_xboole_0|v2_tops_1(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_pre_topc(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.18/0.38  fof(c_0_31, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.38  cnf(c_0_32, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v2_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  cnf(c_0_35, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  fof(c_0_36, plain, ![X23, X24, X25]:(~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~r1_tarski(X24,X25)|r1_tarski(k1_tops_1(X23,X24),k1_tops_1(X23,X25)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.18/0.38  cnf(c_0_37, plain, (X1=k1_xboole_0|~r1_tarski(X1,esk1_1(X1))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.38  cnf(c_0_38, plain, (r1_tarski(k1_tops_1(X1,k1_xboole_0),X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.18/0.38  cnf(c_0_39, negated_conjecture, (v2_tops_1(esk3_0,esk2_0)|X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)|~v3_pre_topc(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  cnf(c_0_40, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.38  cnf(c_0_41, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.38  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.38  cnf(c_0_44, negated_conjecture, (k1_tops_1(X1,X2)=X2|~v2_tops_1(esk3_0,esk2_0)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 0.18/0.38  cnf(c_0_45, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|~v2_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  cnf(c_0_46, plain, (v2_tops_1(X2,X1)|k1_tops_1(X1,X2)!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.38  cnf(c_0_47, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.38  cnf(c_0_48, plain, (k1_tops_1(X1,k1_xboole_0)=k1_xboole_0|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.38  cnf(c_0_49, negated_conjecture, (k1_tops_1(esk2_0,X1)=k1_xboole_0|v2_tops_1(esk3_0,esk2_0)|~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_34]), c_0_35])])).
% 0.18/0.38  cnf(c_0_50, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=k1_xboole_0|~v2_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_34])])).
% 0.18/0.38  cnf(c_0_51, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 0.18/0.38  cnf(c_0_52, negated_conjecture, (k1_tops_1(esk2_0,esk4_0)=esk4_0|~v2_tops_1(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_33]), c_0_34])]), c_0_45])).
% 0.18/0.38  cnf(c_0_53, negated_conjecture, (v2_tops_1(esk3_0,esk2_0)|k1_tops_1(esk2_0,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_42]), c_0_34])])).
% 0.18/0.38  cnf(c_0_54, plain, (r1_tarski(k1_tops_1(X1,X2),k1_xboole_0)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_28])])).
% 0.18/0.38  cnf(c_0_55, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=k1_xboole_0|~m1_subset_1(k1_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_42]), c_0_50])).
% 0.18/0.38  cnf(c_0_56, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.38  cnf(c_0_57, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_51])).
% 0.18/0.38  cnf(c_0_58, negated_conjecture, (k1_tops_1(esk2_0,esk4_0)=esk4_0|k1_tops_1(esk2_0,esk3_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.38  cnf(c_0_59, plain, (r1_tarski(k1_tops_1(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_54])).
% 0.18/0.38  cnf(c_0_60, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=k1_xboole_0|~r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.18/0.38  cnf(c_0_61, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|k1_tops_1(esk2_0,esk3_0)!=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_58]), c_0_34]), c_0_35])])).
% 0.18/0.38  cnf(c_0_62, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~v2_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  cnf(c_0_63, plain, (k1_tops_1(X1,X2)=k1_xboole_0|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_59])).
% 0.18/0.38  cnf(c_0_64, negated_conjecture, (esk4_0!=k1_xboole_0|~v2_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  fof(c_0_65, plain, ![X30, X31, X32]:(~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|(~v3_pre_topc(X31,X30)|~r1_tarski(X31,X32)|r1_tarski(X31,k1_tops_1(X30,X32)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 0.18/0.38  cnf(c_0_66, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_27]), c_0_34]), c_0_42])])).
% 0.18/0.38  cnf(c_0_67, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|k1_tops_1(esk2_0,esk3_0)!=k1_xboole_0|~r1_tarski(esk4_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_61, c_0_56])).
% 0.18/0.38  cnf(c_0_68, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|k1_tops_1(esk2_0,esk3_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_53])).
% 0.18/0.38  cnf(c_0_69, plain, (k1_tops_1(X1,X2)=k1_xboole_0|~l1_pre_topc(X1)|~r1_tarski(X2,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_56]), c_0_26])).
% 0.18/0.38  cnf(c_0_70, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)!=k1_xboole_0|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_53])).
% 0.18/0.38  cnf(c_0_71, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.18/0.38  cnf(c_0_72, negated_conjecture, (v2_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_66])])).
% 0.18/0.38  cnf(c_0_73, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|k1_tops_1(esk2_0,esk3_0)!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_57]), c_0_68])).
% 0.18/0.38  cnf(c_0_74, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)!=k1_xboole_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_58]), c_0_34])]), c_0_70])).
% 0.18/0.38  cnf(c_0_75, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_66]), c_0_34]), c_0_42])])).
% 0.18/0.38  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_72])])).
% 0.18/0.38  cnf(c_0_77, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_66])])).
% 0.18/0.38  cnf(c_0_78, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_66])])).
% 0.18/0.38  cnf(c_0_79, negated_conjecture, (~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_66])])).
% 0.18/0.38  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_78])]), c_0_79]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 81
% 0.18/0.38  # Proof object clause steps            : 54
% 0.18/0.38  # Proof object formula steps           : 27
% 0.18/0.38  # Proof object conjectures             : 35
% 0.18/0.38  # Proof object clause conjectures      : 32
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 22
% 0.18/0.38  # Proof object initial formulas used   : 13
% 0.18/0.38  # Proof object generating inferences   : 27
% 0.18/0.38  # Proof object simplifying inferences  : 47
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 14
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 24
% 0.18/0.38  # Removed in clause preprocessing      : 0
% 0.18/0.38  # Initial clauses in saturation        : 24
% 0.18/0.38  # Processed clauses                    : 300
% 0.18/0.38  # ...of these trivial                  : 7
% 0.18/0.38  # ...subsumed                          : 120
% 0.18/0.38  # ...remaining for further processing  : 173
% 0.18/0.38  # Other redundant clauses eliminated   : 1
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 33
% 0.18/0.38  # Backward-rewritten                   : 30
% 0.18/0.38  # Generated clauses                    : 440
% 0.18/0.38  # ...of the previous two non-trivial   : 367
% 0.18/0.38  # Contextual simplify-reflections      : 13
% 0.18/0.38  # Paramodulations                      : 439
% 0.18/0.38  # Factorizations                       : 0
% 0.18/0.38  # Equation resolutions                 : 1
% 0.18/0.38  # Propositional unsat checks           : 0
% 0.18/0.38  #    Propositional check models        : 0
% 0.18/0.38  #    Propositional check unsatisfiable : 0
% 0.18/0.38  #    Propositional clauses             : 0
% 0.18/0.38  #    Propositional clauses after purity: 0
% 0.18/0.38  #    Propositional unsat core size     : 0
% 0.18/0.38  #    Propositional preprocessing time  : 0.000
% 0.18/0.38  #    Propositional encoding time       : 0.000
% 0.18/0.38  #    Propositional solver time         : 0.000
% 0.18/0.38  #    Success case prop preproc time    : 0.000
% 0.18/0.38  #    Success case prop encoding time   : 0.000
% 0.18/0.38  #    Success case prop solver time     : 0.000
% 0.18/0.38  # Current number of processed clauses  : 86
% 0.18/0.38  #    Positive orientable unit clauses  : 17
% 0.18/0.38  #    Positive unorientable unit clauses: 0
% 0.18/0.38  #    Negative unit clauses             : 3
% 0.18/0.38  #    Non-unit-clauses                  : 66
% 0.18/0.38  # Current number of unprocessed clauses: 76
% 0.18/0.38  # ...number of literals in the above   : 383
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 87
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 2930
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 1373
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 147
% 0.18/0.38  # Unit Clause-clause subsumption calls : 254
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 8
% 0.18/0.38  # BW rewrite match successes           : 8
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 9824
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.044 s
% 0.18/0.38  # System time              : 0.006 s
% 0.18/0.38  # Total time               : 0.050 s
% 0.18/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
