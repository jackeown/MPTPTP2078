%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:05 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 334 expanded)
%              Number of clauses        :   49 ( 128 expanded)
%              Number of leaves         :   12 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  242 (2030 expanded)
%              Number of equality atoms :   30 ( 236 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

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

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_14,negated_conjecture,(
    ! [X37] :
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
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ r1_tarski(X37,esk3_0)
        | ~ v3_pre_topc(X37,esk2_0)
        | X37 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])])).

fof(c_0_15,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | r1_tarski(k1_tops_1(X27,X28),X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_19,plain,(
    ! [X29,X30,X31] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ v3_pre_topc(X30,X29)
      | ~ r1_tarski(X30,X31)
      | r1_tarski(X30,k1_tops_1(X29,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_23])])).

fof(c_0_28,plain,(
    ! [X25,X26] :
      ( ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | v3_pre_topc(k1_tops_1(X25,X26),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X3,u1_struct_0(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_23])])).

cnf(c_0_32,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_37,plain,(
    ! [X4,X5,X7,X8,X9] :
      ( ( r2_hidden(esk1_2(X4,X5),X4)
        | r1_xboole_0(X4,X5) )
      & ( r2_hidden(esk1_2(X4,X5),X5)
        | r1_xboole_0(X4,X5) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | ~ r1_xboole_0(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_38,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_39,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X17,X19)
      | ~ r1_xboole_0(X18,X19)
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,k1_tops_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_23])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tops_1(esk2_0,esk3_0))
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( v2_tops_1(esk3_0,esk2_0)
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0)
    | ~ v3_pre_topc(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk2_0,X1),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_23])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | r1_xboole_0(X20,k4_xboole_0(X22,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)))
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_32]),c_0_41]),c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_51,plain,(
    ! [X32,X33] :
      ( ( ~ v2_tops_1(X33,X32)
        | k1_tops_1(X32,X33) = k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) )
      & ( k1_tops_1(X32,X33) != k1_xboole_0
        | v2_tops_1(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

cnf(c_0_52,negated_conjecture,
    ( k1_tops_1(esk2_0,X1) = k1_xboole_0
    | v2_tops_1(esk3_0,esk2_0)
    | ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_47])).

fof(c_0_57,plain,(
    ! [X12,X13] :
      ( ( k4_xboole_0(X12,X13) != k1_xboole_0
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | k4_xboole_0(X12,X13) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_tops_1(esk3_0,esk2_0)
    | ~ r1_tarski(esk4_0,X1)
    | ~ r1_xboole_0(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_59,plain,
    ( v2_tops_1(X2,X1)
    | k1_tops_1(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( k1_tops_1(esk2_0,X1) = k1_xboole_0
    | v2_tops_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_25]),c_0_26])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( ~ v2_tops_1(esk3_0,esk2_0)
    | ~ r1_xboole_0(k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_41])).

cnf(c_0_65,negated_conjecture,
    ( v2_tops_1(X1,esk2_0)
    | k1_tops_1(esk2_0,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_23])).

cnf(c_0_66,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = k1_xboole_0
    | v2_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_17]),c_0_27])])).

cnf(c_0_68,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_17])])).

cnf(c_0_71,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_23]),c_0_17])])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_71]),c_0_71]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n015.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:08:23 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.41  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.18/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.41  #
% 0.18/0.41  # Preprocessing time       : 0.028 s
% 0.18/0.41  # Presaturation interreduction done
% 0.18/0.41  
% 0.18/0.41  # Proof found!
% 0.18/0.41  # SZS status Theorem
% 0.18/0.41  # SZS output start CNFRefutation
% 0.18/0.41  fof(t86_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 0.18/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.41  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.18/0.41  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.18/0.41  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 0.18/0.41  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.18/0.41  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.18/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.41  fof(t67_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 0.18/0.41  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.18/0.41  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 0.18/0.41  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.18/0.41  fof(c_0_12, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t86_tops_1])).
% 0.18/0.41  fof(c_0_13, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.41  fof(c_0_14, negated_conjecture, ![X37]:((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v2_tops_1(esk3_0,esk2_0))&(((r1_tarski(esk4_0,esk3_0)|~v2_tops_1(esk3_0,esk2_0))&(v3_pre_topc(esk4_0,esk2_0)|~v2_tops_1(esk3_0,esk2_0)))&(esk4_0!=k1_xboole_0|~v2_tops_1(esk3_0,esk2_0))))&(v2_tops_1(esk3_0,esk2_0)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk2_0)))|(~r1_tarski(X37,esk3_0)|~v3_pre_topc(X37,esk2_0)|X37=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])])).
% 0.18/0.41  fof(c_0_15, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_tarski(X15,X16)|r1_tarski(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.18/0.41  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.41  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  fof(c_0_18, plain, ![X27, X28]:(~l1_pre_topc(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|r1_tarski(k1_tops_1(X27,X28),X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.18/0.41  fof(c_0_19, plain, ![X29, X30, X31]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|(~v3_pre_topc(X30,X29)|~r1_tarski(X30,X31)|r1_tarski(X30,k1_tops_1(X29,X31)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 0.18/0.41  cnf(c_0_20, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.41  cnf(c_0_21, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.41  cnf(c_0_22, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.41  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_24, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.41  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.41  cnf(c_0_26, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.41  cnf(c_0_27, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_23])])).
% 0.18/0.41  fof(c_0_28, plain, ![X25, X26]:(~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|v3_pre_topc(k1_tops_1(X25,X26),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.18/0.41  cnf(c_0_29, plain, (r1_tarski(X1,k1_tops_1(X2,X3))|~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X3,u1_struct_0(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.41  cnf(c_0_30, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.18/0.41  cnf(c_0_31, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_17]), c_0_23])])).
% 0.18/0.41  cnf(c_0_32, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)|~v2_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_33, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~v2_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v2_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_35, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.41  cnf(c_0_36, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  fof(c_0_37, plain, ![X4, X5, X7, X8, X9]:(((r2_hidden(esk1_2(X4,X5),X4)|r1_xboole_0(X4,X5))&(r2_hidden(esk1_2(X4,X5),X5)|r1_xboole_0(X4,X5)))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|~r1_xboole_0(X7,X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.18/0.41  fof(c_0_38, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.41  fof(c_0_39, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_tarski(X17,X19)|~r1_xboole_0(X18,X19)|X17=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).
% 0.18/0.41  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_23])])).
% 0.18/0.41  cnf(c_0_41, negated_conjecture, (r1_tarski(esk4_0,k1_tops_1(esk2_0,esk3_0))|~v2_tops_1(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])).
% 0.18/0.41  cnf(c_0_42, negated_conjecture, (v2_tops_1(esk3_0,esk2_0)|X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)|~v3_pre_topc(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_43, negated_conjecture, (v3_pre_topc(k1_tops_1(esk2_0,X1),esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_23])])).
% 0.18/0.41  cnf(c_0_44, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.41  cnf(c_0_45, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.41  fof(c_0_46, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|r1_xboole_0(X20,k4_xboole_0(X22,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.18/0.41  cnf(c_0_47, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.41  cnf(c_0_48, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.41  cnf(c_0_49, negated_conjecture, (r1_tarski(esk4_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)))|~v2_tops_1(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_32]), c_0_41]), c_0_34])).
% 0.18/0.41  cnf(c_0_50, negated_conjecture, (esk4_0!=k1_xboole_0|~v2_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  fof(c_0_51, plain, ![X32, X33]:((~v2_tops_1(X33,X32)|k1_tops_1(X32,X33)=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))&(k1_tops_1(X32,X33)!=k1_xboole_0|v2_tops_1(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.18/0.41  cnf(c_0_52, negated_conjecture, (k1_tops_1(esk2_0,X1)=k1_xboole_0|v2_tops_1(esk3_0,esk2_0)|~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.41  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.18/0.41  cnf(c_0_54, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.41  cnf(c_0_55, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.41  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_47])).
% 0.18/0.41  fof(c_0_57, plain, ![X12, X13]:((k4_xboole_0(X12,X13)!=k1_xboole_0|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|k4_xboole_0(X12,X13)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.18/0.41  cnf(c_0_58, negated_conjecture, (~v2_tops_1(esk3_0,esk2_0)|~r1_tarski(esk4_0,X1)|~r1_xboole_0(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.18/0.41  cnf(c_0_59, plain, (v2_tops_1(X2,X1)|k1_tops_1(X1,X2)!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.18/0.41  cnf(c_0_60, negated_conjecture, (k1_tops_1(esk2_0,X1)=k1_xboole_0|v2_tops_1(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,X1),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_25]), c_0_26])).
% 0.18/0.41  cnf(c_0_61, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.18/0.41  cnf(c_0_62, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.41  cnf(c_0_63, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.18/0.41  cnf(c_0_64, negated_conjecture, (~v2_tops_1(esk3_0,esk2_0)|~r1_xboole_0(k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_58, c_0_41])).
% 0.18/0.41  cnf(c_0_65, negated_conjecture, (v2_tops_1(X1,esk2_0)|k1_tops_1(esk2_0,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_59, c_0_23])).
% 0.18/0.41  cnf(c_0_66, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.18/0.41  cnf(c_0_67, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=k1_xboole_0|v2_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_17]), c_0_27])])).
% 0.18/0.41  cnf(c_0_68, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.18/0.41  cnf(c_0_69, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_56])).
% 0.18/0.41  cnf(c_0_70, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)!=k1_xboole_0|~r1_xboole_0(k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_17])])).
% 0.18/0.41  cnf(c_0_71, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_23]), c_0_17])])).
% 0.18/0.41  cnf(c_0_72, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.18/0.41  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_71]), c_0_71]), c_0_72])]), ['proof']).
% 0.18/0.41  # SZS output end CNFRefutation
% 0.18/0.41  # Proof object total steps             : 74
% 0.18/0.41  # Proof object clause steps            : 49
% 0.18/0.41  # Proof object formula steps           : 25
% 0.18/0.41  # Proof object conjectures             : 29
% 0.18/0.41  # Proof object clause conjectures      : 26
% 0.18/0.41  # Proof object formula conjectures     : 3
% 0.18/0.41  # Proof object initial clauses used    : 23
% 0.18/0.41  # Proof object initial formulas used   : 12
% 0.18/0.41  # Proof object generating inferences   : 24
% 0.18/0.41  # Proof object simplifying inferences  : 27
% 0.18/0.41  # Training examples: 0 positive, 0 negative
% 0.18/0.41  # Parsed axioms                        : 12
% 0.18/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.41  # Initial clauses                      : 26
% 0.18/0.41  # Removed in clause preprocessing      : 0
% 0.18/0.41  # Initial clauses in saturation        : 26
% 0.18/0.41  # Processed clauses                    : 1041
% 0.18/0.41  # ...of these trivial                  : 13
% 0.18/0.41  # ...subsumed                          : 614
% 0.18/0.41  # ...remaining for further processing  : 414
% 0.18/0.41  # Other redundant clauses eliminated   : 2
% 0.18/0.41  # Clauses deleted for lack of memory   : 0
% 0.18/0.41  # Backward-subsumed                    : 13
% 0.18/0.41  # Backward-rewritten                   : 136
% 0.18/0.41  # Generated clauses                    : 1908
% 0.18/0.41  # ...of the previous two non-trivial   : 1316
% 0.18/0.41  # Contextual simplify-reflections      : 34
% 0.18/0.41  # Paramodulations                      : 1905
% 0.18/0.41  # Factorizations                       : 0
% 0.18/0.41  # Equation resolutions                 : 3
% 0.18/0.41  # Propositional unsat checks           : 0
% 0.18/0.41  #    Propositional check models        : 0
% 0.18/0.41  #    Propositional check unsatisfiable : 0
% 0.18/0.41  #    Propositional clauses             : 0
% 0.18/0.41  #    Propositional clauses after purity: 0
% 0.18/0.41  #    Propositional unsat core size     : 0
% 0.18/0.41  #    Propositional preprocessing time  : 0.000
% 0.18/0.41  #    Propositional encoding time       : 0.000
% 0.18/0.41  #    Propositional solver time         : 0.000
% 0.18/0.41  #    Success case prop preproc time    : 0.000
% 0.18/0.41  #    Success case prop encoding time   : 0.000
% 0.18/0.41  #    Success case prop solver time     : 0.000
% 0.18/0.41  # Current number of processed clauses  : 238
% 0.18/0.41  #    Positive orientable unit clauses  : 24
% 0.18/0.41  #    Positive unorientable unit clauses: 2
% 0.18/0.41  #    Negative unit clauses             : 4
% 0.18/0.41  #    Non-unit-clauses                  : 208
% 0.18/0.41  # Current number of unprocessed clauses: 267
% 0.18/0.41  # ...number of literals in the above   : 766
% 0.18/0.41  # Current number of archived formulas  : 0
% 0.18/0.41  # Current number of archived clauses   : 174
% 0.18/0.41  # Clause-clause subsumption calls (NU) : 16548
% 0.18/0.41  # Rec. Clause-clause subsumption calls : 12504
% 0.18/0.41  # Non-unit clause-clause subsumptions  : 472
% 0.18/0.41  # Unit Clause-clause subsumption calls : 321
% 0.18/0.41  # Rewrite failures with RHS unbound    : 23
% 0.18/0.41  # BW rewrite match attempts            : 67
% 0.18/0.41  # BW rewrite match successes           : 6
% 0.18/0.41  # Condensation attempts                : 0
% 0.18/0.41  # Condensation successes               : 0
% 0.18/0.41  # Termbank termtop insertions          : 26615
% 0.18/0.42  
% 0.18/0.42  # -------------------------------------------------
% 0.18/0.42  # User time                : 0.087 s
% 0.18/0.42  # System time              : 0.002 s
% 0.18/0.42  # Total time               : 0.089 s
% 0.18/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
