%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 778 expanded)
%              Number of clauses        :   52 ( 290 expanded)
%              Number of leaves         :    6 ( 190 expanded)
%              Depth                    :   13
%              Number of atoms          :  292 (8078 expanded)
%              Number of equality atoms :    9 ( 110 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   39 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & r1_tarski(X4,X2)
                    & r2_hidden(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_1)).

fof(t54_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,k1_tops_1(X1,X3))
          <=> ? [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                & v3_pre_topc(X4,X1)
                & r1_tarski(X4,X3)
                & r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> ? [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                      & v3_pre_topc(X4,X1)
                      & r1_tarski(X4,X2)
                      & r2_hidden(X3,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_tops_1])).

fof(c_0_7,plain,(
    ! [X17,X18,X19,X21] :
      ( ( m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r2_hidden(X18,k1_tops_1(X17,X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v3_pre_topc(esk2_3(X17,X18,X19),X17)
        | ~ r2_hidden(X18,k1_tops_1(X17,X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r1_tarski(esk2_3(X17,X18,X19),X19)
        | ~ r2_hidden(X18,k1_tops_1(X17,X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(X18,esk2_3(X17,X18,X19))
        | ~ r2_hidden(X18,k1_tops_1(X17,X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v3_pre_topc(X21,X17)
        | ~ r1_tarski(X21,X19)
        | ~ r2_hidden(X18,X21)
        | r2_hidden(X18,k1_tops_1(X17,X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_tops_1])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X25,X27,X29] :
      ( v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & ( ~ r2_hidden(esk5_0,esk4_0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v3_pre_topc(X25,esk3_0)
        | ~ r1_tarski(X25,esk4_0)
        | ~ r2_hidden(esk5_0,X25)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | r2_hidden(esk5_0,esk4_0)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( v3_pre_topc(esk6_0,esk3_0)
        | r2_hidden(esk5_0,esk4_0)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( r1_tarski(esk6_0,esk4_0)
        | r2_hidden(esk5_0,esk4_0)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( r2_hidden(esk5_0,esk6_0)
        | r2_hidden(esk5_0,esk4_0)
        | ~ v3_pre_topc(esk4_0,esk3_0) )
      & ( m1_subset_1(esk7_1(X27),k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ r2_hidden(X27,esk4_0)
        | v3_pre_topc(esk4_0,esk3_0) )
      & ( v3_pre_topc(esk7_1(X27),esk3_0)
        | ~ r2_hidden(X27,esk4_0)
        | v3_pre_topc(esk4_0,esk3_0) )
      & ( r1_tarski(esk7_1(X27),esk4_0)
        | ~ r2_hidden(X27,esk4_0)
        | v3_pre_topc(esk4_0,esk3_0) )
      & ( r2_hidden(X27,esk7_1(X27))
        | ~ r2_hidden(X27,esk4_0)
        | v3_pre_topc(esk4_0,esk3_0) )
      & ( ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v3_pre_topc(X29,esk3_0)
        | ~ r1_tarski(X29,esk4_0)
        | ~ r2_hidden(X27,X29)
        | r2_hidden(X27,esk4_0)
        | v3_pre_topc(esk4_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X4,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk7_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v3_pre_topc(esk7_1(X1),esk3_0)
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk7_1(X1),esk4_0)
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk7_1(X3))
    | ~ r2_hidden(X3,esk4_0)
    | ~ r1_tarski(esk7_1(X3),X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | r1_tarski(esk7_1(esk1_2(esk4_0,X1)),esk4_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk7_1(X1))
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_23,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_24,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | r1_tarski(k1_tops_1(X15,X16),X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0)
    | ~ r1_tarski(esk4_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_17]),c_0_12]),c_0_13])])).

cnf(c_0_27,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk5_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | r2_hidden(X1,k1_tops_1(esk3_0,esk4_0))
    | r1_tarski(esk4_0,X2)
    | ~ r2_hidden(X1,esk7_1(esk1_2(esk4_0,X2))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_17])]),c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | r2_hidden(esk1_2(esk4_0,X1),esk7_1(esk1_2(esk4_0,X1)))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,X2))
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk1_2(X1,k1_tops_1(esk3_0,X2)),esk4_0)
    | ~ r1_tarski(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( ~ v3_pre_topc(esk2_3(esk3_0,X1,X2),esk3_0)
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk5_0,esk2_3(esk3_0,X1,X2))
    | ~ r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ r1_tarski(esk2_3(esk3_0,X1,X2),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_12]),c_0_13])])).

cnf(c_0_36,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | r2_hidden(esk1_2(esk4_0,X1),k1_tops_1(esk3_0,esk4_0))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k1_tops_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tops_1(esk3_0,X1))
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_16])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk5_0,esk2_3(esk3_0,X2,X1))
    | ~ r2_hidden(X2,k1_tops_1(esk3_0,X1))
    | ~ r1_tarski(esk2_3(esk3_0,X2,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_12]),c_0_13])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,esk2_3(X2,X1,X3))
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_43,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(esk5_0,esk4_0)
    | ~ r1_tarski(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_17])).

fof(c_0_44,plain,(
    ! [X13,X14] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | v3_pre_topc(k1_tops_1(X13,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_45,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_17]),c_0_12]),c_0_40])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk5_0,k1_tops_1(esk3_0,X1))
    | ~ r1_tarski(esk2_3(esk3_0,esk5_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_12]),c_0_13])])).

cnf(c_0_48,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | r2_hidden(esk5_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_50,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk3_0)
    | r2_hidden(esk5_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_51,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_40])])).

cnf(c_0_52,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_45]),c_0_17]),c_0_12])]),c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(esk5_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_17]),c_0_12]),c_0_13])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk6_0)
    | ~ r1_tarski(esk6_0,X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_49]),c_0_12]),c_0_13])]),c_0_50]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_17]),c_0_12]),c_0_13])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(esk5_0,esk6_0)
    | ~ r1_tarski(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_17])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | r2_hidden(esk5_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_56])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk6_0)
    | ~ r1_tarski(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_56])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_56])]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk6_0,esk4_0)
    | r2_hidden(esk5_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_56])]),c_0_59]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t57_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X2))&r2_hidden(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tops_1)).
% 0.20/0.38  fof(t54_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.20/0.38  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.20/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X2))&r2_hidden(X3,X4))))))), inference(assume_negation,[status(cth)],[t57_tops_1])).
% 0.20/0.38  fof(c_0_7, plain, ![X17, X18, X19, X21]:(((((m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))|~r2_hidden(X18,k1_tops_1(X17,X19))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(v3_pre_topc(esk2_3(X17,X18,X19),X17)|~r2_hidden(X18,k1_tops_1(X17,X19))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(r1_tarski(esk2_3(X17,X18,X19),X19)|~r2_hidden(X18,k1_tops_1(X17,X19))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(r2_hidden(X18,esk2_3(X17,X18,X19))|~r2_hidden(X18,k1_tops_1(X17,X19))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X17)))|~v3_pre_topc(X21,X17)|~r1_tarski(X21,X19)|~r2_hidden(X18,X21)|r2_hidden(X18,k1_tops_1(X17,X19))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_tops_1])])])])])).
% 0.20/0.38  fof(c_0_8, negated_conjecture, ![X25, X27, X29]:((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(((~r2_hidden(esk5_0,esk4_0)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v3_pre_topc(X25,esk3_0)|~r1_tarski(X25,esk4_0)|~r2_hidden(esk5_0,X25))|~v3_pre_topc(esk4_0,esk3_0))&((((m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0))&(v3_pre_topc(esk6_0,esk3_0)|r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)))&(r1_tarski(esk6_0,esk4_0)|r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)))&(r2_hidden(esk5_0,esk6_0)|r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0))))&(((((m1_subset_1(esk7_1(X27),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X27,esk4_0)|v3_pre_topc(esk4_0,esk3_0))&(v3_pre_topc(esk7_1(X27),esk3_0)|~r2_hidden(X27,esk4_0)|v3_pre_topc(esk4_0,esk3_0)))&(r1_tarski(esk7_1(X27),esk4_0)|~r2_hidden(X27,esk4_0)|v3_pre_topc(esk4_0,esk3_0)))&(r2_hidden(X27,esk7_1(X27))|~r2_hidden(X27,esk4_0)|v3_pre_topc(esk4_0,esk3_0)))&(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v3_pre_topc(X29,esk3_0)|~r1_tarski(X29,esk4_0)|~r2_hidden(X27,X29)|r2_hidden(X27,esk4_0)|v3_pre_topc(esk4_0,esk3_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.20/0.38  fof(c_0_9, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_10, plain, (r2_hidden(X4,k1_tops_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r1_tarski(X1,X3)|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk7_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (v3_pre_topc(esk7_1(X1),esk3_0)|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (r1_tarski(esk7_1(X1),esk4_0)|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (~r2_hidden(esk5_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v3_pre_topc(X1,esk3_0)|~r1_tarski(X1,esk4_0)|~r2_hidden(esk5_0,X1)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|r2_hidden(X1,k1_tops_1(esk3_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk7_1(X3))|~r2_hidden(X3,esk4_0)|~r1_tarski(esk7_1(X3),X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|r1_tarski(esk7_1(esk1_2(esk4_0,X1)),esk4_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,esk7_1(X1))|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  fof(c_0_23, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  fof(c_0_24, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|r1_tarski(k1_tops_1(X15,X16),X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.20/0.38  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,X2))|~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk4_0)|~r1_tarski(esk4_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_17]), c_0_12]), c_0_13])])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk5_0,X1)|~r1_tarski(X1,esk4_0)), inference(csr,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.38  cnf(c_0_28, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,k1_tops_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|r2_hidden(X1,k1_tops_1(esk3_0,esk4_0))|r1_tarski(esk4_0,X2)|~r2_hidden(X1,esk7_1(esk1_2(esk4_0,X2)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_17])]), c_0_16])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|r2_hidden(esk1_2(esk4_0,X1),esk7_1(esk1_2(esk4_0,X1)))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_16])).
% 0.20/0.38  cnf(c_0_31, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_32, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,X2))|~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk1_2(X1,k1_tops_1(esk3_0,X2)),esk4_0)|~r1_tarski(esk4_0,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.38  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (~v3_pre_topc(esk2_3(esk3_0,X1,X2),esk3_0)|~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk5_0,esk2_3(esk3_0,X1,X2))|~r2_hidden(X1,k1_tops_1(esk3_0,X2))|~r1_tarski(esk2_3(esk3_0,X1,X2),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_12]), c_0_13])])).
% 0.20/0.38  cnf(c_0_36, plain, (v3_pre_topc(esk2_3(X1,X2,X3),X1)|~r2_hidden(X2,k1_tops_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|r2_hidden(esk1_2(esk4_0,X1),k1_tops_1(esk3_0,esk4_0))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.38  cnf(c_0_38, plain, (k1_tops_1(X1,X2)=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(X2,k1_tops_1(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (r1_tarski(esk4_0,k1_tops_1(esk3_0,X1))|~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_16])).
% 0.20/0.38  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk5_0,esk2_3(esk3_0,X2,X1))|~r2_hidden(X2,k1_tops_1(esk3_0,X1))|~r1_tarski(esk2_3(esk3_0,X2,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_12]), c_0_13])])).
% 0.20/0.38  cnf(c_0_42, plain, (r2_hidden(X1,esk2_3(X2,X1,X3))|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(esk5_0,esk4_0)|~r1_tarski(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_17])).
% 0.20/0.38  fof(c_0_44, plain, ![X13, X14]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|v3_pre_topc(k1_tops_1(X13,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_37])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_17]), c_0_12]), c_0_40])])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk5_0,k1_tops_1(esk3_0,X1))|~r1_tarski(esk2_3(esk3_0,esk5_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_12]), c_0_13])])).
% 0.20/0.38  cnf(c_0_48, plain, (r1_tarski(esk2_3(X1,X2,X3),X3)|~r2_hidden(X2,k1_tops_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (v3_pre_topc(esk6_0,esk3_0)|r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_40])])).
% 0.20/0.38  cnf(c_0_52, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_45]), c_0_17]), c_0_12])]), c_0_46])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(esk5_0,k1_tops_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_17]), c_0_12]), c_0_13])])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,X2))|~v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk6_0)|~r1_tarski(esk6_0,X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_49]), c_0_12]), c_0_13])]), c_0_50]), c_0_51])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_17]), c_0_12]), c_0_13])])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(esk5_0,esk6_0)|~r1_tarski(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_17])])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (~r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_56])])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (~r2_hidden(esk5_0,esk6_0)|~r1_tarski(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_56])])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_56])]), c_0_59])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (r1_tarski(esk6_0,esk4_0)|r2_hidden(esk5_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, (~r1_tarski(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_56])]), c_0_59]), c_0_63]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 65
% 0.20/0.38  # Proof object clause steps            : 52
% 0.20/0.38  # Proof object formula steps           : 13
% 0.20/0.38  # Proof object conjectures             : 41
% 0.20/0.38  # Proof object clause conjectures      : 38
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 24
% 0.20/0.38  # Proof object initial formulas used   : 6
% 0.20/0.38  # Proof object generating inferences   : 20
% 0.20/0.38  # Proof object simplifying inferences  : 59
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 6
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 26
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 26
% 0.20/0.38  # Processed clauses                    : 101
% 0.20/0.38  # ...of these trivial                  : 4
% 0.20/0.38  # ...subsumed                          : 25
% 0.20/0.38  # ...remaining for further processing  : 71
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 3
% 0.20/0.38  # Backward-rewritten                   : 38
% 0.20/0.38  # Generated clauses                    : 104
% 0.20/0.38  # ...of the previous two non-trivial   : 102
% 0.20/0.38  # Contextual simplify-reflections      : 9
% 0.20/0.38  # Paramodulations                      : 102
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 28
% 0.20/0.38  #    Positive orientable unit clauses  : 9
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 17
% 0.20/0.38  # Current number of unprocessed clauses: 27
% 0.20/0.38  # ...number of literals in the above   : 106
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 41
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 649
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 161
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 34
% 0.20/0.38  # Unit Clause-clause subsumption calls : 13
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 13
% 0.20/0.38  # BW rewrite match successes           : 4
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 4840
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.033 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
